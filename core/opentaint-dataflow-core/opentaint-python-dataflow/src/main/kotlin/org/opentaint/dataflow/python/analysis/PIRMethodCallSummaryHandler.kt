package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler.SummaryEdge
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.alias.forEachAliasAfterCallStatement
import org.opentaint.ir.api.python.PIRCall
import kotlin.collections.plusAssign

class PIRMethodCallSummaryHandler(
    private val callInst: PIRCall,
    private val ctx: PIRMethodAnalysisContext,
    private val callResolver: PIRCallResolver, // TODO remove call resolver
    private val apManager: ApManager,
    override val factTypeChecker: FactTypeChecker,
) : MethodCallSummaryHandler {
    private val factMapper get() = ctx.methodCallFactMapper

    private val resolvedMethods by lazy { callResolver.resolveCall(callInst) }

    private val summaryRewriter by lazy {
        PIRCallRuleBasedSummaryRewriter(callInst, ctx, apManager, resolvedMethods)
    }

    override fun prepareFactToFactSummary(summaryEdge: Edge.FactToFact): List<Edge.FactToFact> =
        summaryRewriter.rewriteSummaryFact(summaryEdge.factAp).map { (resultFact, refinement) ->
            Edge.FactToFact(
                summaryEdge.methodEntryPoint,
                refinement.refineFact(summaryEdge.initialFactAp),
                summaryEdge.statement,
                refinement.refineFact(resultFact),
            )
        }

    override fun prepareNDFactToFactSummary(summaryEdge: Edge.NDFactToFact): List<Edge.NDFactToFact> =
        summaryRewriter.rewriteSummaryFact(summaryEdge.factAp).map { (resultFact, refinement) ->
            check(!refinement.hasRefinement) { "Can't refine NDF2F edge" }
            Edge.NDFactToFact(
                summaryEdge.methodEntryPoint,
                summaryEdge.initialFacts,
                summaryEdge.statement,
                resultFact,
            )
        }

    /**
     * Translates a callee-frame exit fact into the caller's frame.
     *
     * Mirror of the enter pipeline (mapper produces offset-free output,
     * then [PIRMethodCallResolver] applies [PIRMethodCallFactMapper.offsetEnter]):
     * [PIRMethodCallFactMapper.offsetExit] first maps the real callee frame back
     * to the offset-free frame (`Argument(0)` → `This`, `Argument(i)` →
     * `Argument(i - offset)`), then the offset-blind mapper rebases onto the
     * caller's call-site values.
     */
    override fun mapMethodExitToReturnFlowFact(fact: FinalFactAp): List<FinalFactAp> {
        val callee = resolvedMethods.firstOrNull() ?: return emptyList()
        val offsetFreeBase = factMapper.offsetExit(callInst, callee, fact.base) ?: return emptyList()
        return factMapper.mapMethodExitToReturnFlowFact(callInst, fact.rebase(offsetFreeBase), factTypeChecker)
    }

    override fun handleZeroToZero(summaryFact: FinalFactAp?): Set<Sequent> =
        super.handleZeroToZero(summaryFact).flatMapTo(hashSetOf()) { seq ->
            if (seq !is Sequent.ZeroToFact) return@flatMapTo listOf(seq)

            val result = mutableListOf(seq)
            ctx.aliasAnalysis?.forEachAliasAfterCallStatement(callInst, seq.factAp) { aliased ->
                result += Sequent.ZeroToFact(aliased, seq.traceInfo)
            }
            result
        }

    override fun handleSummary(
        currentFactAp: FinalFactAp,
        summaryEffect: MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication,
        summaryEdge: SummaryEdge,
        createSideEffectRequirement: (refinement: ExclusionSet) -> Sequent?,
        handleSummaryEdge: (initialFactRefinement: ExclusionSet?, summaryFactAp: FinalFactAp) -> Sequent
    ): Set<Sequent> {
        val result = hashSetOf<Sequent>()

        result += super.handleSummary(
            currentFactAp,
            summaryEffect,
            summaryEdge,
            createSideEffectRequirement,
        ) { initialFactRefinement: ExclusionSet?, summaryFactAp: FinalFactAp ->
            if (initialFactRefinement != null) {
                createSideEffectRequirement(initialFactRefinement)?.also { result.add(it) }
            }

            if (summaryEdge.hasMemoryEffect()) {
                ctx.aliasAnalysis?.forEachAliasAfterCallStatement(callInst, summaryFactAp) { aliased ->
                    result += handleSummaryEdge(initialFactRefinement, aliased)
                }
            }

            handleSummaryEdge(initialFactRefinement, summaryFactAp)
        }

        return result
    }

    private fun SummaryEdge.hasMemoryEffect(): Boolean {
        if (this !is SummaryEdge.F2F) return true
        return !final.equalTo(initial)
    }
}
