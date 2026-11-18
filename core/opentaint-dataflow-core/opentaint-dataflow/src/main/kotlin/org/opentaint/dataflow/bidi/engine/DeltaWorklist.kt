package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.ir.api.common.cfg.CommonInst

/** Ordinary input queues. Completed output deduplication belongs to MethodEdgeStore. */
class DeltaWorklist(
    private val flowFirst: Boolean = false,
    batchManager: ApManager? = null,
    private val priorityManager: ApManager? = null,
) {
    private val zero = ArrayList<EdgeDelta>()
    private val readyFlow = ArrayList<EdgeDelta>()
    private val ready = ArrayList<EdgeDelta>()
    private val flow = ArrayList<EdgeDelta>()
    private val other = ArrayList<Any>() // EdgeDelta or PendingWork.MarkedBatch
    private val batches = batchManager?.let(::NeutralBatchWorklist)

    val isEmpty: Boolean get() = size == 0
    val hasZeroWork: Boolean get() = zero.isNotEmpty()
    internal val hasFlowWork: Boolean get() = readyFlow.isNotEmpty() || flow.isNotEmpty()
    val size: Int get() = zero.size + readyFlow.size + ready.size + flow.size + other.size

    fun add(delta: EdgeDelta) {
        if (!RuntimeDataDomain.packet(delta.premise, delta.facts)) return
        val priority = priorityManager
        if (priority == null || delta.zeroToZero) {
            addPacket(delta)
            return
        }
        delta.facts.forEachPriorityPacket(priority) {
            addPacket(if (it === delta.facts) delta else delta.copy(facts = it))
        }
    }

    private fun addPacket(delta: EdgeDelta) {
        when {
            delta.zeroToZero -> zero += delta
            priorityManager != null && delta.facts.isReadyPriority -> {
                if (delta.facts is FlowTree) readyFlow += delta else ready += delta
            }
            (flowFirst || priorityManager != null) && delta.facts is FlowTree -> flow += delta
            else -> {
                val admission = if (!hasZeroWork) batches?.offer(delta) else null
                if (admission == null) other += delta
                else if (admission.newlyQueued) other += admission.work
            }
        }
    }

    fun removeNext(): EdgeDelta = when (val work = removeItem()) {
        is EdgeDelta -> work
        is PendingWork.MarkedBatch -> {
            val (initial, facts) = work.batch.removeFirst()
            addBatch(work.node, work.batch)
            EdgeDelta(initial, work.node, facts)
        }
        else -> error("Unknown work item")
    }

    fun removeNextBatch(): PendingWork = when (val work = removeItem()) {
        is EdgeDelta -> PendingWork.Scalar(work)
        is PendingWork.MarkedBatch -> work
        else -> error("Unknown work item")
    }

    private fun removeItem(): Any {
        zero.removeLastOrNull()?.let { return it }
        readyFlow.removeLastOrNull()?.let { return it }
        ready.removeLastOrNull()?.let { return it }
        flow.removeLastOrNull()?.let { return it }
        val work = other.removeLast()
        if (work is PendingWork.MarkedBatch) batches?.removed(work)
        return work
    }

    /** Retain an unfinished quantum before any work barrier or yield. */
    fun addBatch(node: CommonInst, batch: NeutralRelationBatch) {
        if (batch.isEmpty) return
        val admission = batches?.retain(node, batch)
        if (admission == null) other += PendingWork.MarkedBatch(node, batch)
        else if (admission.newlyQueued) other += admission.work
    }

    fun clear() {
        zero.clear()
        readyFlow.clear()
        ready.clear()
        flow.clear()
        other.clear()
        batches?.clear()
    }
}

internal val Facts.isReadyPriority: Boolean
    get() = layer == Layer.NORMAL || when (this) {
        is Reach -> true
        is FlowTree -> tail == Tail.EXACT
        is TaintTree -> !root.hasAny
    }

internal inline fun Facts.forEachPriorityPacket(ap: ApManager, emit: (Facts) -> Unit) {
    if (this !is TaintTree || layer == Layer.NORMAL || !root.hasAny) {
        emit(this)
        return
    }
    val exact = ap.taintAlg.mapLeaves(root, ap.cancellation) { ap.taintLeaves(it.exact, MarkSet.EMPTY) }
    if (exact == null) {
        emit(this)
        return
    }
    val rest = ap.taintAlg.mapLeaves(root, ap.cancellation) { ap.taintLeaves(MarkSet.EMPTY, it.any) }
    emit(withRoot(exact))
    emit(withRoot(checkNotNull(rest)))
}
