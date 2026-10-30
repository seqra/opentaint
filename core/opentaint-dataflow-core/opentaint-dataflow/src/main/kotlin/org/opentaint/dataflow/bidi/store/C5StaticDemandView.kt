package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.InitialAp
import org.opentaint.dataflow.bidi.ap.Pattern

/** C5 can reject a packed label before graph-owner tests and endpoint allocation. */
internal fun interface StaticCandidateFilter {
    fun keep(from: Pattern, to: Pattern, marks: GuidanceMarks): Boolean
}

/** Internal capability; packed storage and its geometry stay private to the snapshot. */
internal interface C5StaticDemandView : StaticDemandView {
    fun c5Targets(actual: Pattern, prefixesOnly: Boolean, keep: StaticCandidateFilter): Sequence<StaticGuidanceEdge>
    fun c5Incoming(input: Pattern, flowOnly: Boolean, keep: StaticCandidateFilter): Sequence<StaticGuidanceEdge>
    fun c5HasComposedEndpoints(initial: InitialAp, outputs: List<Pattern>, keepTarget: StaticCandidateFilter): Boolean
    fun selectedTargets(actual: Pattern, prefixesOnly: Boolean, query: StaticRowQuery,
                        keep: StaticCandidateFilter): Sequence<StaticGuidanceEdge> = c5Targets(actual, prefixesOnly, keep)
    fun selectedIncoming(input: Pattern, query: StaticRowQuery,
                         keep: StaticCandidateFilter): Sequence<StaticGuidanceEdge> = c5Incoming(input, false, keep)
    fun selectedHasComposedEndpoints(initial: InitialAp, outputs: List<Pattern>, query: StaticRowQuery,
                                     keep: StaticCandidateFilter): Boolean = c5HasComposedEndpoints(initial, outputs, keep)
}

internal fun StaticDemandView.filteredTargets(
    actual: Pattern, prefixesOnly: Boolean, keep: StaticCandidateFilter,
): Sequence<StaticGuidanceEdge> = when (this) {
    is C5StaticDemandView -> c5Targets(actual, prefixesOnly, keep)
    else -> targets(actual, prefixesOnly).filter { keep.keep(it.from, it.to, it.marks) }
}

internal fun StaticDemandView.filteredIncoming(
    input: Pattern, flowOnly: Boolean, keep: StaticCandidateFilter,
): Sequence<StaticGuidanceEdge> = when (this) {
    is C5StaticDemandView -> c5Incoming(input, flowOnly, keep)
    else -> incoming(input, flowOnly).filter { keep.keep(it.from, it.to, it.marks) }
}

internal fun StaticDemandView.filteredHasComposedEndpoints(
    initial: InitialAp, outputs: List<Pattern>, keepTarget: StaticCandidateFilter,
): Boolean = when (this) {
    is C5StaticDemandView -> c5HasComposedEndpoints(initial, outputs, keepTarget)
    // A coarse fallback is sufficient: filteredTargets will discard impossible seeds.
    else -> hasComposedEndpoints(initial, outputs)
}

internal fun StaticDemandView.selectedTargets(
    actual: Pattern, prefixesOnly: Boolean, query: StaticRowQuery, keep: StaticCandidateFilter,
): Sequence<StaticGuidanceEdge> = when (this) {
    is C5StaticDemandView -> selectedTargets(actual, prefixesOnly, query, keep)
    else -> filteredTargets(actual, prefixesOnly, keep)
}

internal fun StaticDemandView.selectedIncoming(
    input: Pattern, query: StaticRowQuery, keep: StaticCandidateFilter,
): Sequence<StaticGuidanceEdge> = when (this) {
    is C5StaticDemandView -> selectedIncoming(input, query, keep)
    else -> filteredIncoming(input, false, keep)
}

internal fun StaticDemandView.selectedHasComposedEndpoints(
    initial: InitialAp, outputs: List<Pattern>, query: StaticRowQuery, keep: StaticCandidateFilter,
): Boolean = when (this) {
    is C5StaticDemandView -> selectedHasComposedEndpoints(initial, outputs, query, keep)
    else -> filteredHasComposedEndpoints(initial, outputs, keep)
}
