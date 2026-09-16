package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
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

        if (handleUnfoldRequest(summaryEffect, kind)) {
            return emptySet()
        }

        // The question travels from a callee to its callers ALONG THE VALUE it is about. A static is
        // not a value a caller passed: `AccessPathBase.ClassStatic` is one global singleton shared by
        // every frame that touches any static, so re-posting the question on it does not ask a caller
        // anything -- it publishes the question program-wide, and every frame then stores its own
        // copy. Measured on tms: 86% of stored side effect summaries sit on static bases.
        if (currentInitialFactAp.base is AccessPathBase.ClassStatic) {
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
