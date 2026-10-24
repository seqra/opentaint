package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.ApManager
import org.opentaint.ir.api.common.cfg.CommonInst

/** An actor either evaluates one original scalar item or one exact diagonal
 * mask. A fallback consumes that mask incrementally and retains the remainder. */
sealed interface PendingWork {
    class Scalar(val delta: EdgeDelta) : PendingWork
    class MarkedBatch(val node: CommonInst, val batch: NeutralRelationBatch,
                      val unchanged: Boolean = false) : PendingWork
}

/** Pending changed cohorts only. Unchanged work retains its original scalar
 * order/repeat contract, including the ZERO phase. There is one input tree per
 * cohort and an exact mark mask, with no per-mark scalar input archive. */
internal class NeutralBatchWorklist(private val m: ApManager) {
    private data class Key(val node: CommonInst, val geometry: Any)
    data class Admission(val work: PendingWork.MarkedBatch, val newlyQueued: Boolean)
    private val pending = HashMap<Key, PendingWork.MarkedBatch>()

    fun offer(delta: EdgeDelta): Admission? {
        m.cancellation.checkpoint()
        val batch = NeutralRelationBatch.from(m, delta.premise, delta.facts) ?: return null
        return retain(delta.node, batch)
    }

    /** The marks were already admitted. This path does not rerun the unchanged
     * repeat gate when a caller retains an unfinished quantum or scalar fallback. */
    fun retain(node: CommonInst, batch: NeutralRelationBatch): Admission {
        m.cancellation.checkpoint()
        check(!batch.isEmpty) { "An empty mask is not pending work" }
        val key = Key(node, batch.geometryKey)
        val previous = pending[key]
        if (previous != null) {
            check(previous.batch.mergeIfSameGeometry(batch)) { "A cohort key must identify one complete geometry" }
            return Admission(previous, newlyQueued = false)
        }
        val work = PendingWork.MarkedBatch(node, batch)
        pending[key] = work
        return Admission(work, newlyQueued = true)
    }

    fun removed(work: PendingWork.MarkedBatch) {
        val key = Key(work.node, work.batch.geometryKey)
        if (pending[key] === work) pending.remove(key)
    }

    fun clear() = pending.clear()
}
