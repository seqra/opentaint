package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.ApManager
import org.opentaint.dataflow.bidi.ap.FlowTree
import org.opentaint.dataflow.bidi.ap.TaintNode
import org.opentaint.dataflow.bidi.ap.TaintTree
import org.opentaint.ir.api.common.cfg.CommonInst

/** The repeat set spans all unchanged lanes. ZERO keeps its original phase policy. */
class DeltaWorklist(private val flowFirst: Boolean = false, batchManager: ApManager? = null) {
    // A scalar is retained directly, as before batching. The other permitted
    // item type is MarkedBatch; wrapping every scalar would add one retained
    // object per pending item in later runs and in the GROUP fallback.
    private class Unchanged(val item: Any, val sequence: Long)
    // Ordinary EdgeDelta equality deliberately excludes annotation metadata.
    private data class RepeatKey(val delta: EdgeDelta, val nonSubsumable: TaintNode?)

    private val unchanged = ArrayList<Unchanged>()
    private val flowUnchanged = ArrayList<Unchanged>()
    private val taintUnchanged = ArrayList<Unchanged>()
    private val seen = HashSet<Any>()
    private var sequence = 0L
    private var zeroUnchanged = 0
    private val zero = ArrayList<EdgeDelta>()
    private val flow = ArrayList<EdgeDelta>()
    private val other = ArrayList<Any>() // EdgeDelta or PendingWork.MarkedBatch
    private val batches = batchManager?.let(::NeutralBatchWorklist)

    private val unchangedEmpty: Boolean get() =
        unchanged.isEmpty() && flowUnchanged.isEmpty() && taintUnchanged.isEmpty()
    val isEmpty: Boolean get() = unchangedEmpty && zero.isEmpty() && flow.isEmpty() && other.isEmpty()
    val hasZeroWork: Boolean get() = zero.isNotEmpty() || zeroUnchanged != 0
    val size: Int get() = unchanged.size + flowUnchanged.size + taintUnchanged.size +
        zero.size + flow.size + other.size

    fun add(delta: EdgeDelta) {
        when {
            delta.zeroToZero -> zero += delta
            flowFirst && delta.facts is FlowTree -> flow += delta
            else -> {
                // Do not change the global unchanged/ZERO phase order. Only
                // changed work outside that phase joins pending mark cohorts.
                val admission = if (!hasZeroWork) batches?.offer(delta) else null
                if (admission == null) other += delta
                else if (admission.newlyQueued) other += admission.work
            }
        }
    }

    fun addUnchanged(delta: EdgeDelta): Boolean {
        val mask = (delta.facts as? TaintTree)?.nonSubsumable
        val repeatKey = if (mask == null) delta else RepeatKey(delta, mask)
        if (!seen.add(repeatKey)) return false
        val lane = when {
            !flowFirst || delta.zeroToZero -> unchanged
            delta.facts is FlowTree -> flowUnchanged
            else -> taintUnchanged
        }
        lane += Unchanged(delta, sequence++)
        if (delta.zeroToZero) zeroUnchanged++
        return true
    }

    fun removeNext(): EdgeDelta {
        return when (val work = removeItem()) {
            is EdgeDelta -> work
            is PendingWork.MarkedBatch -> {
                val (initial, facts) = work.batch.removeFirst()
                addBatch(work.node, work.batch, work.unchanged)
                EdgeDelta(initial, work.node, facts)
            }
            else -> error("Unknown work item")
        }
    }

    /** A removed cohort has no index entry. New successors can enqueue their
     * own masks while the caller processes this immutable geometry. */
    fun removeNextBatch(): PendingWork {
        return when (val work = removeItem()) {
            is EdgeDelta -> PendingWork.Scalar(work)
            is PendingWork.MarkedBatch -> work
            else -> error("Unknown work item")
        }
    }

    private fun removeItem(): Any {
        if (!flowFirst || hasZeroWork) {
            // While ZERO is pending, retain the original global unchanged LIFO order.
            latestUnchanged().removeLastOrNull()?.item?.let {
                if ((it as? EdgeDelta)?.zeroToZero == true) zeroUnchanged--
                return it
            }
            zero.removeLastOrNull()?.let { return it }
        }
        val work = flowUnchanged.removeLastOrNull()?.item ?: flow.removeLastOrNull() ?:
            taintUnchanged.removeLastOrNull()?.item ?: other.removeLast()
        if (work is PendingWork.MarkedBatch) batches?.removed(work)
        return work
    }

    /** Retain an already admitted remainder before afterProcess or any queue
     * barrier. Unchanged continuations are never coalesced or deduplicated. */
    fun addBatch(node: CommonInst, batch: NeutralRelationBatch, unchanged: Boolean = false) {
        if (batch.isEmpty) return
        if (unchanged) {
            taintUnchanged += Unchanged(PendingWork.MarkedBatch(node, batch, true), sequence++)
            return
        }
        val admission = batches?.retain(node, batch)
        if (admission == null) other += PendingWork.MarkedBatch(node, batch)
        else if (admission.newlyQueued) other += admission.work
    }

    private fun latestUnchanged(): ArrayList<Unchanged> {
        var latest = unchanged
        if ((flowUnchanged.lastOrNull()?.sequence ?: -1L) > (latest.lastOrNull()?.sequence ?: -1L))
            latest = flowUnchanged
        if ((taintUnchanged.lastOrNull()?.sequence ?: -1L) > (latest.lastOrNull()?.sequence ?: -1L))
            latest = taintUnchanged
        return latest
    }

    /** Call after processing and successors, including after the final item of a Work event. */
    fun afterProcess() {
        if (unchangedEmpty) seen.clear()
    }

    fun clear() {
        unchanged.clear()
        flowUnchanged.clear()
        taintUnchanged.clear()
        seen.clear()
        zero.clear()
        flow.clear()
        other.clear()
        batches?.clear()
        zeroUnchanged = 0
        sequence = 0L
    }
}
