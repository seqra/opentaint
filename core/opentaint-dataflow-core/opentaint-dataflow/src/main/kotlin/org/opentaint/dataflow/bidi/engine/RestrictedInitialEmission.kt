package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.BoundAdmission

internal data class RestrictedOfferPlan(
    val initials: Set<AdmittedInitial>,
    val possibleAdmissions: Set<BoundAdmission>,
)

/** Complete fixed-run admission, evaluated once in the caller on the original offer. */
internal fun emitRestrictedInitials(
    config: RunConfig,
    ops: ApOps,
    callee: MethodKey,
    actual: Facts,
    statistics: N2Statistics? = null,
): List<AdmittedInitial> {
    return prepareRestrictedOffer(config, ops, callee, actual, statistics).initials.toList()
}

internal fun prepareRestrictedOffer(
    config: RunConfig,
    ops: ApOps,
    callee: MethodKey,
    actual: Facts,
    statistics: N2Statistics? = null,
): RestrictedOfferPlan {
    check(config.restricted)
    val ap = ops.manager
    val result = LinkedHashSet<AdmittedInitial>()
    var possible: MutableSet<BoundAdmission>? = null
    ops.limit(actual, config.fieldLimit, config.mode.demandRefinement, object : ApOut {
        override fun markRequest(mark: TaintMark): Nothing = error("A field cut cannot request a mark")
        override fun result(bounded: Facts) {
            for (leaf in ops.leaves(bounded)) {
                ap.cancellation.checkpoint()
                if (config.index == 2) validateRun2StaticFullInput(ap, leaf, config.fieldLimit)
            }
            val demand = checkNotNull(config.demand)
            if (config.mode.demandRefinement && bounded !is Reach) {
                for (command in demand.boundInitials(callee, bounded, config.admissionPolicy) { leaf ->
                    savedInitialGuards(config, callee, null, leaf)
                }) {
                    result += command.admitted
                    if (command.possible && command.qualification != null) {
                        val set = possible ?: LinkedHashSet<BoundAdmission>().also { possible = it }
                        set += command
                    }
                }
            } else result.addAll(demand.initials(callee, bounded, config.admissionPolicy))
        }
    })
    statistics?.demandLookupCompleted(result.isNotEmpty())
    return RestrictedOfferPlan(result, possible.orEmpty())
}

/** Frozen records only. A new child or a current reply cannot add guard fields. */
internal fun savedInitialGuards(
    config: RunConfig, method: MethodKey, scope: BlockScope?, actual: Pattern,
): Sequence<Pattern> = sequence {
    val store = config.records
    val direct = if (scope == null) store.byEntry(method, actual) else store.byEntry(method, scope, actual)
    for (record in direct) if (record.direction == config.direction) yield(record.premise.toPattern())
    val opposite = if (scope == null) store.byExit(method, actual) else store.byExit(method, scope, actual)
    for (record in opposite) if (record.direction != config.direction) {
        for (view in record.reversedAt(actual)) yield(view.premise)
    }
}
