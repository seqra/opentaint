package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.AnyDemandCursor
import org.opentaint.dataflow.bidi.store.BlockScope

internal data class LoopPrecisionCursor(val scope: BlockScope, val family: LoopAdmissionFamily,
                                        val cursor: AnyDemandCursor)

/** One scalar query. A witness rejects early budgets; it never replaces the full observer. */
internal class LoopRestrictionSession<R>(
    private val ops: ApOps,
    private val policy: RestrictedInitialPolicy,
    val observe: (Facts) -> LoopObservation<R>,
    private val precision: (Pattern) -> List<LoopPrecisionCursor>?,
) {
    /** The former certificate assumes an ANY/DEMAND primary. The expanded family has no such
     * invariant. Keep the complete observer until a whole-family certificate is proved. */
    @Suppress("UNUSED_PARAMETER")
    fun certifiedFirstBudget(raw: Facts, baseline: LoopObservation<R>): Int? = null
}
