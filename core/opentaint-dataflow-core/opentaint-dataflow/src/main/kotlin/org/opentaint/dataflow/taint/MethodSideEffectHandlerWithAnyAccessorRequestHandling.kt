package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSideEffectSummaryHandler

interface MethodSideEffectHandlerWithAnyAccessorRequestHandling : MethodSideEffectSummaryHandler {
    val runner: AnalysisRunner

    override fun handleZeroToFact(
        currentFactAp: FinalFactAp,
        summaryEffect: SummaryEdgeApplication,
        kind: SideEffectKind
    ): Set<MethodSequentFlowFunction.Sequent> {
        if (kind !is TaintMarkFieldUnfoldRequest) {
            return super.handleZeroToFact(currentFactAp, summaryEffect, kind)
        }

        handleUnfoldRequest(summaryEffect, kind, f2f = false)
        return emptySet()
    }

    override fun handleFactToFact(
        methodEntryPoint: MethodEntryPoint,
        currentInitialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
        summaryEffect: SummaryEdgeApplication,
        kind: SideEffectKind
    ): Set<MethodSequentFlowFunction.Sequent> {
        if (kind !is TaintMarkFieldUnfoldRequest) {
            return super.handleFactToFact(methodEntryPoint, currentInitialFactAp, currentFactAp, summaryEffect, kind)
        }

        if (handleUnfoldRequest(summaryEffect, kind, f2f = true)) {
            return emptySet()
        }

        val nextRequests = kind.nextRequests(summaryEffect)
        val ex = when (summaryEffect) {
            is SummaryEdgeApplication.SummaryApRefinement -> ExclusionSet.Empty
            is SummaryEdgeApplication.SummaryExclusionRefinement -> summaryEffect.exclusion
        }
        val fact = currentInitialFactAp.replaceExclusions(ex)
        return nextRequests.mapTo(hashSetOf()) {
            MethodSequentFlowFunction.Sequent.FactSideEffect(fact, it)
        }
    }

    private fun TaintMarkFieldUnfoldRequest.nextRequests(
        effect: SummaryEdgeApplication
    ): List<TaintMarkFieldUnfoldRequest> = when (effect) {
        is SummaryEdgeApplication.SummaryExclusionRefinement -> listOf(this)
        is SummaryEdgeApplication.SummaryApRefinement -> {
            if (suffix != null || effect.delta.isEmpty) {
                listOf(this)
            } else {
                // One request carrying every candidate, not one request per candidate. The answer
                // demands the whole set, which is a superset of what any single fork would have
                // demanded -- and on the registration channel a larger exclusion set spawns MORE
                // abstractions, never fewer. So recall is preserved while the climb stops
                // multiplying by the delta's width at every frame it passes through.
                listOf(runner.manager.internSideEffectKind(copy(suffix = effect.delta.startAccessors())))
            }
        }
    }

    private fun handleUnfoldRequest(
        summaryEffect: SummaryEdgeApplication,
        request: TaintMarkFieldUnfoldRequest,
        f2f: Boolean
    ): Boolean {
        when (summaryEffect) {
            is SummaryEdgeApplication.SummaryApRefinement -> {
                if (!summaryEffect.delta.isEmpty) {
                    return handleMarkAfterAnyFieldRequest(summaryEffect.delta, request, f2f)
                }
            }

            is SummaryEdgeApplication.SummaryExclusionRefinement -> {
                // taint mark requested -> mark not in initial fact, delta is empty -> mark not in fact
            }
        }

        return false
    }

    private fun handleMarkAfterAnyFieldRequest(
        delta: FinalFactAp.Delta,
        request: TaintMarkFieldUnfoldRequest,
        f2f: Boolean
    ): Boolean {
        val mark = request.mark
        // `getAllAccessors` costs the delta's PATH count and allocates two sets plus an interner
        // lookup per accessor, and every one of those is thrown away here: the only question asked
        // is membership. `containsAccessorDeep` is the same predicate with an early exit and a
        // DAG-aware visited set.
        if (!delta.containsAccessorDeep(mark)) return false

        // Freshness is asked of every candidate before one is chosen, not of the chosen one
        // afterwards: the two narrowings would otherwise compound, and a stale nearest candidate
        // would hide a fresh one behind it.
        val demand = runner.manager.markUnfoldDemand
        val fresh = { accessor: Accessor ->
            !demand.alreadyDemanded(request.method, request.fact.base, mark, accessor)
        }

        val candidates = if (request.suffix != null) emptyList() else delta.markCandidates(mark)

        // Nothing to split off. An `ExclusionSet.Empty` requirement demands nothing -- the fact it
        // refines is the fact itself, so `handleInputFactChange` returns at its equality guard, and
        // `handleMethodSideEffectRequirement` drops an `Empty` refinement outright. Posting it only
        // broadcasts a requirement to every caller of the asking frame for each of them to rebase,
        // delta and discard. The pre-climb handler returned here rather than posting.
        if (request.suffix == null && candidates.isEmpty()) return true

        val selected = request.suffix?.filter(fresh)
            ?: candidates.filter { fresh(it.accessor) }.selectAnswer(mark, extraPaths(f2f))

        val nextAccessors = demand.demand(request.method, request.fact.base, mark, selected)

        // Every accessor this answer would contribute has been demanded for this question
        // already, so the split it asks for has been asked for. The request is NOT consumed: it
        // keeps climbing, because a caller further up may still hold an accessor nobody has
        // contributed. Consuming it here measurably stalls the analysis instead.
        if (nextAccessors.isEmpty()) return false

        val exclusion = nextAccessors.fold(ExclusionSet.Empty as ExclusionSet, ExclusionSet::add)
        runner.manager.handleCrossUnitSideEffectReq(request.method, request.fact.replaceExclusions(exclusion))

        return true
    }

    /**
     * How many answers beyond the nearest one a request on this edge may carry.
     *
     * None on a fact-to-fact edge. An answer there becomes a side-effect requirement that every
     * caller of the asking frame replays, and the fact it refines is usually one the demand itself
     * produced, so a second answer there is a second branch of an iteration with no fixed point on
     * self-similar shapes. A zero-to-fact answer is about a value built locally -- low fan-in --
     * and is where the width given up by answering with the nearest candidate is bought back.
     *
     * Measured on tms: widening fact-to-fact answers too costs 45% more request traffic and finds
     * nothing extra.
     */
    private fun extraPaths(f2f: Boolean): Int = if (f2f) 0 else EXTRA_Z2F_PATHS

    private fun FinalFactAp.Delta.startAccessors(): Set<Accessor> {
        val startAccessors = hashSetOf<Accessor>()
        for (accessor in getStartAccessors()) {
            if (accessor !is AnyAccessor) {
                startAccessors.add(accessor)
                continue
            }

            val anySuccessors = readAccessor(accessor)?.getStartAccessors()
                ?: continue

            anySuccessors.filterTo(startAccessors) { it !is AnyAccessor }
        }
        return startAccessors
    }

    private companion object {
        const val EXTRA_Z2F_PATHS = 2
    }
}
