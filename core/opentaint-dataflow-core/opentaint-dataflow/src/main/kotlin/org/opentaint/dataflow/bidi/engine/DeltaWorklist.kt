package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.ApManager
import org.opentaint.dataflow.bidi.ap.FlowTree
import org.opentaint.ir.api.common.cfg.CommonInst

/** Ordinary input queues. Completed output deduplication belongs to MethodEdgeStore. */
class DeltaWorklist(private val flowFirst: Boolean = false, batchManager: ApManager? = null) {
    private val zero = ArrayList<EdgeDelta>()
    private val flow = ArrayList<EdgeDelta>()
    private val other = ArrayList<Any>() // EdgeDelta or PendingWork.MarkedBatch
    private val batches = batchManager?.let(::NeutralBatchWorklist)

    val isEmpty: Boolean get() = zero.isEmpty() && flow.isEmpty() && other.isEmpty()
    val hasZeroWork: Boolean get() = zero.isNotEmpty()
    val size: Int get() = zero.size + flow.size + other.size

    fun add(delta: EdgeDelta) {
        when {
            delta.zeroToZero -> zero += delta
            flowFirst && delta.facts is FlowTree -> flow += delta
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
        flow.clear()
        other.clear()
        batches?.clear()
    }
}
