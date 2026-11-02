package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*

/** A C2 entry can have several exits. Their indexes are borrowed, not copied or composed.
 * C5 selects an exact exit first, so that view has one complete producer port pair. */
internal fun unionStaticDemandViews(views: List<C5StaticDemandView>): StaticDemandView =
    if (views.size == 1) views.single() else UnionStaticDemandView(views)

private class UnionStaticDemandView(private val views: List<C5StaticDemandView>) : C5StaticDemandView {
    private fun <T> union(query: (C5StaticDemandView) -> Sequence<T>): Sequence<T> =
        views.asSequence().flatMap(query).distinct()

    override fun targetInputs() = union { it.targetInputs() }
    override fun entries(actual: Pattern) = union { it.entries(actual) }
    override fun targets(actual: Pattern, prefixesOnly: Boolean) = union { it.targets(actual, prefixesOnly) }
    override fun flowTargets(actual: Pattern) = union { it.flowTargets(actual) }
    override fun pairs(initial: InitialAp, outputs: List<Pattern>) = union { it.pairs(initial, outputs) }
    override fun incoming(input: Pattern, flowOnly: Boolean) = union { it.incoming(input, flowOnly) }
    override fun outgoing(output: Pattern) = union { it.outgoing(output) }
    override fun markedOutputs(mark: TaintMark) = union { it.markedOutputs(mark) }
    override fun estimatedMarkedOutputs(mark: TaintMark) = views.sumOf { it.estimatedMarkedOutputs(mark) }
    override fun hasMarkedOutput(input: Pattern, mark: TaintMark) = views.any { it.hasMarkedOutput(input, mark) }
    override fun hasComposedEndpoints(initial: InitialAp, outputs: List<Pattern>) =
        views.any { it.hasComposedEndpoints(initial, outputs) }
    override fun c5Targets(actual: Pattern, prefixesOnly: Boolean, keep: StaticCandidateFilter) =
        union { it.c5Targets(actual, prefixesOnly, keep) }
    override fun c5Incoming(input: Pattern, flowOnly: Boolean, keep: StaticCandidateFilter) =
        union { it.c5Incoming(input, flowOnly, keep) }
    override fun c5HasComposedEndpoints(initial: InitialAp, outputs: List<Pattern>, keepTarget: StaticCandidateFilter) =
        views.any { it.c5HasComposedEndpoints(initial, outputs, keepTarget) }
    override fun selectedTargets(actual: Pattern, prefixesOnly: Boolean, query: StaticRowQuery, keep: StaticCandidateFilter) =
        union { it.selectedTargets(actual, prefixesOnly, query, keep) }
    override fun selectedIncoming(input: Pattern, query: StaticRowQuery, keep: StaticCandidateFilter) =
        union { it.selectedIncoming(input, query, keep) }
    override fun selectedHasComposedEndpoints(initial: InitialAp, outputs: List<Pattern>, query: StaticRowQuery,
                                             keep: StaticCandidateFilter) =
        views.any { it.selectedHasComposedEndpoints(initial, outputs, query, keep) }
}
