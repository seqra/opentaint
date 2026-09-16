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
import org.opentaint.dataflow.util.ClimbKey
import org.opentaint.dataflow.util.UnfoldClimbBound

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

        if (!UnfoldClimbBound.admit(requestKey("z2f", kind, summaryEffect))) {
            return emptySet()
        }

        if (UnfoldClimbBound.questionAlreadyAsked(questionKey("z2f", kind))) {
            return emptySet()
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
        if (kind !is TaintMarkFieldUnfoldRequest || UnfoldClimbBound.disabled) {
            return super.handleFactToFact(methodEntryPoint, currentInitialFactAp, currentFactAp, summaryEffect, kind)
        }

        if (!UnfoldClimbBound.admit(requestKey("f2f@$methodEntryPoint", kind, summaryEffect))) {
            return emptySet()
        }

        if (UnfoldClimbBound.questionAlreadyAsked(questionKey("f2f@$methodEntryPoint", kind))) {
            return emptySet()
        }

        // 8867fb730's guard: fact-to-fact edges vastly outnumber zero-to-fact ones, so refining on
        // all of them does not terminate. Only act while the request is still the bare abstraction.
        if (UnfoldClimbBound.unrefinedOnly && !kind.fact.getAllAccessors().isEmpty()) {
            UnfoldClimbBound.droppedByRefined.incrementAndGet()
            return super.handleFactToFact(methodEntryPoint, currentInitialFactAp, currentFactAp, summaryEffect, kind)
        }

        if (handleUnfoldRequest(summaryEffect, kind)) {
            UnfoldClimbBound.answeredLocally.incrementAndGet()
            return emptySet()
        }

        val suffix = when (summaryEffect) {
            is SummaryEdgeApplication.SummaryExclusionRefinement -> kind.suffix
            is SummaryEdgeApplication.SummaryApRefinement -> {
                kind.suffix ?: summaryEffect.delta.takeIf { !it.isEmpty }
            }
        }

        val newKind = kind.copy(suffix = suffix)
        val fact = currentInitialFactAp.replaceExclusions(ExclusionSet.Empty)

        // The climb is otherwise unbounded: `fact` is the caller's fact, one access step longer
        // each hop, with its exclusions erased. Under recursion it never converges.
        UnfoldClimbBound.noteDepth(fact.depth)

        if (UnfoldClimbBound.exceedsDepth(fact.depth)) {
            UnfoldClimbBound.droppedByDepth.incrementAndGet()
            return emptySet()
        }

        if (UnfoldClimbBound.isDuplicate(ClimbKey(methodEntryPoint, currentInitialFactAp, newKind))) {
            UnfoldClimbBound.droppedByMemo.incrementAndGet()
            return emptySet()
        }

        UnfoldClimbBound.reposted.incrementAndGet()
        return setOf(MethodSequentFlowFunction.Sequent.FactSideEffect(fact, newKind))
    }

    /** The question, without the summary-application detail that makes it look distinct. */
    private fun questionKey(site: String, request: TaintMarkFieldUnfoldRequest): Any =
        listOf(site, request.method, request.fact, request.mark)

    private fun requestKey(
        site: String,
        request: TaintMarkFieldUnfoldRequest,
        summaryEffect: SummaryEdgeApplication
    ): String {
        val effect = when (summaryEffect) {
            is SummaryEdgeApplication.SummaryApRefinement -> "ApRefinement"
            is SummaryEdgeApplication.SummaryExclusionRefinement -> "ExclusionRefinement"
        }
        val delta = (summaryEffect as? SummaryEdgeApplication.SummaryApRefinement)?.delta
        return UnfoldClimbBound.requestKey(
            method = "$site:${request.method}",
            fact = request.fact,
            mark = request.mark,
            effect = effect,
            delta = delta,
            suffix = request.suffix,
        )
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

        val nextAccessors = request.suffix?.startAccessors()
            ?: delta.relevantStartAccessors(mark)

        val exclusion = nextAccessors.fold(ExclusionSet.Empty as ExclusionSet, ExclusionSet::add)
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
