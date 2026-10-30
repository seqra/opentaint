package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*

/** Complete fixed-run admission, evaluated once in the caller on the original offer. */
internal fun emitRestrictedInitials(
    config: RunConfig,
    ops: ApOps,
    callee: MethodKey,
    actual: Facts,
    statistics: N2Statistics? = null,
): List<InitialAp> {
    check(config.restricted)
    val ap = ops.manager
    val result = LinkedHashSet<InitialAp>()
    ops.limit(actual, config.fieldLimit, object : ApOut {
        override fun markRequest(mark: TaintMark): Nothing = error("A field cut cannot request a mark")
        override fun result(bounded: Facts) {
            for (leaf in ops.leaves(bounded)) {
                ap.cancellation.checkpoint()
                if (config.index == 2) validateRun2StaticFullInput(ap, leaf, config.fieldLimit)
            }
            result.addAll(checkNotNull(config.demand).initials(callee, bounded, config.admissionPolicy))
        }
    })
    statistics?.demandLookupCompleted(result.isNotEmpty())
    return result.toList()
}
