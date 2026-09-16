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

        handleUnfoldRequest(summaryEffect, kind)
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

        // A request asks about an ABSTRACTION: is the mark hidden under the `[any]` of this fact?
        // A fact that already carries accessors is not an abstraction waiting for an answer -- it is
        // one, produced by answering the question at the abstraction above it. Answering there
        // refines it again, and the refined frame re-raises the question one accessor further down.
        //
        // Measured on tms: that iteration registers 3.3x the side-effect requirements (299,593 vs
        // 90,644), and each registration fans out ~14 new initial facts instead of ~3, for 6.46M
        // initial facts against 335k. That difference is the whole distance between finishing in
        // 77 s and dying on the memory guard.
        if (!kind.fact.getAllAccessors().isEmpty()) {
            return super.handleFactToFact(methodEntryPoint, currentInitialFactAp, currentFactAp, summaryEffect, kind)
        }

        if (handleUnfoldRequest(summaryEffect, kind)) {
            return emptySet()
        }

        val nextRequests = kind.nextRequests(summaryEffect)
        val fact = currentInitialFactAp.replaceExclusions(ExclusionSet.Empty)
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
                effect.delta.startAccessors().map { copy(suffix = it) }
            }
        }
    }

    private fun handleUnfoldRequest(
        summaryEffect: SummaryEdgeApplication,
        request: TaintMarkFieldUnfoldRequest
    ): Boolean {
        when (summaryEffect) {
            is SummaryEdgeApplication.SummaryApRefinement -> {
                if (!summaryEffect.delta.isEmpty) {
                    return handleMarkAfterAnyFieldRequest(summaryEffect.delta, request)
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
        request: TaintMarkFieldUnfoldRequest
    ): Boolean {
        val mark = request.mark
        val allAccessors = delta.getAllAccessors()
        if (mark !in allAccessors) return false

        val nextAccessors = request.suffix?.let { setOf(it) }
            ?: delta.relevantStartAccessors(mark)

        // The demand for one question only grows. An accessor that has already been demanded for it
        // does not refine the abstraction a second time -- the split it asks for ends in `[any]`
        // again, one accessor further down, and re-raises the same question. See [MarkUnfoldDemand].
        val newAccessors = runner.manager.markUnfoldDemand.newlyDemanded(
            request.method, request.fact.base, mark, nextAccessors
        )

        // Nothing fresh: this answer asks for a split that has already been asked for. Raising it
        // again cannot refine anything, so no request is issued. The request itself is not consumed
        // -- it keeps travelling, because a different caller may still hold an accessor no one has
        // contributed yet, and stopping it here measurably loses that.
        if (newAccessors.isEmpty()) return false

        val exclusion = newAccessors.fold(ExclusionSet.Empty as ExclusionSet, ExclusionSet::add)
        runner.manager.handleCrossUnitSideEffectReq(request.method, request.fact.replaceExclusions(exclusion))

        return true
    }

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

    private fun FinalFactAp.Delta.relevantStartAccessors(mark: Accessor): List<Accessor> =
        startAccessors().filter { accessor ->
            accessor == mark || readAccessor(accessor)?.getAllAccessors()?.contains(mark) ?: false
        }
}
