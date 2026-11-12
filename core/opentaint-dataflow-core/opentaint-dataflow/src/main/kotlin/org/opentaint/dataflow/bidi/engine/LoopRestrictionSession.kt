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
    private val probe: ((Facts, Set<LoopAdmissionDescriptor>) -> LoopAdmissionProbe)? = null,
    private val observeCompleted: ((Facts, LoopAdmissionBundle) -> LoopObservation<R>)? = null,
    private val precision: (Pattern) -> List<LoopPrecisionCursor>?,
) {
    private var expectedBaseline: LoopObservation<R>? = null
    private var expectedDescriptors: Set<LoopAdmissionDescriptor> = emptySet()

    /** Full equality remains mandatory after a completed, non-rejected probe. */
    fun trial(candidate: Facts, baseline: LoopObservation<R>): LoopObservation<R>? {
        val scan = probe ?: return observe(candidate)
        if (expectedBaseline !== baseline) {
            expectedDescriptors = baseline.labelledAdmissions.mapTo(HashSet()) {
                LoopAdmissionDescriptor(it.scope, it.family, it.admitted.initial.toPattern(), it.admitted.layer)
            }
            expectedBaseline = baseline
        }
        return when (val result = scan(candidate, expectedDescriptors)) {
            is LoopAdmissionProbe.Rejected -> null
            is LoopAdmissionProbe.Complete -> observeCompleted?.invoke(candidate, result.bundle) ?: observe(candidate)
            LoopAdmissionProbe.Unsupported -> observe(candidate)
        }
    }

    /** The former certificate assumes an ANY/DEMAND primary. The expanded family has no such
     * invariant. Keep the complete observer until a whole-family certificate is proved. */
    @Suppress("UNUSED_PARAMETER")
    fun certifiedFirstBudget(raw: Facts, baseline: LoopObservation<R>): Int? = null
}
