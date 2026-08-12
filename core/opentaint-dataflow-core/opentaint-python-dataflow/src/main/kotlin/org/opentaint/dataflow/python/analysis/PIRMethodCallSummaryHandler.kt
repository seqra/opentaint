package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler.SummaryEdge
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.alias.forEachAliasBeforeCallStatement
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRFunction
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

    private fun FinalFactAp.toCallerFrame(callee: PIRFunction): FinalFactAp? =
        factMapper.toCallerFrame(callInst, callee, base)?.let { rebase(it) }

    private val MethodEntryPoint.callee: PIRFunction get() = method as PIRFunction

    override fun prepareZeroToFactSummary(summaryEdge: Edge.ZeroToFact): List<Edge.ZeroToFact> {
        val callerFrameFact = summaryEdge.factAp.toCallerFrame(summaryEdge.methodEntryPoint.callee) ?: return emptyList()
        return listOf(Edge.ZeroToFact(summaryEdge.methodEntryPoint, summaryEdge.statement, callerFrameFact))
    }

    override fun prepareFactToFactSummary(summaryEdge: Edge.FactToFact): List<Edge.FactToFact> {
        val callerFrameFact = summaryEdge.factAp.toCallerFrame(summaryEdge.methodEntryPoint.callee) ?: return emptyList()
        return summaryRewriter.rewriteSummaryFact(callerFrameFact).map { (resultFact, refinement) ->
            Edge.FactToFact(
                summaryEdge.methodEntryPoint,
                refinement.refineFact(summaryEdge.initialFactAp),
                summaryEdge.statement,
                refinement.refineFact(resultFact),
            )
        }
    }

    override fun prepareNDFactToFactSummary(summaryEdge: Edge.NDFactToFact): List<Edge.NDFactToFact> {
        val callerFrameFact = summaryEdge.factAp.toCallerFrame(summaryEdge.methodEntryPoint.callee) ?: return emptyList()
        return summaryRewriter.rewriteSummaryFact(callerFrameFact).map { (resultFact, refinement) ->
            check(!refinement.hasRefinement) { "Can't refine NDF2F edge" }
            Edge.NDFactToFact(
                summaryEdge.methodEntryPoint,
                summaryEdge.initialFacts,
                summaryEdge.statement,
                resultFact,
            )
        }
    }

    override fun mapMethodExitToReturnFlowFact(fact: FinalFactAp): List<FinalFactAp> =
        factMapper.mapMethodExitToReturnFlowFact(callInst, fact, factTypeChecker)

    override fun handleZeroToZero(summaryFact: FinalFactAp?): Set<Sequent> =
        super.handleZeroToZero(summaryFact).flatMapTo(hashSetOf()) { seq ->
            if (seq !is Sequent.ZeroToFact) return@flatMapTo listOf(seq)

            val result = mutableListOf(seq)
            ctx.aliasAnalysis?.forEachAliasBeforeCallStatement(callInst, seq.factAp) { aliased ->
                result += Sequent.ZeroToFact(aliased, seq.traceInfo)
            }
            result
        }

    override fun handleSummary(
        currentFactAp: FinalFactAp,
        summaryEffect: MethodSummaryEdgeApplicationUtils.EdgeRefinement,
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
                ctx.aliasAnalysis?.forEachAliasBeforeCallStatement(callInst, summaryFactAp) { aliased ->
                    result += handleSummaryEdge(initialFactRefinement, aliased)
                }
            }

            handleSummaryEdge(initialFactRefinement, summaryFactAp)
        }

        return result
    }

    private fun SummaryEdge.hasMemoryEffect(): Boolean {
        if (this !is SummaryEdge.F2F) return true
        val callerFrameInitial = factMapper.toCallerFrame(callInst, methodEntryPoint.callee, initial.base)
            ?.let { initial.rebase(it) } ?: return true
        return !final.equalTo(callerFrameInitial)
    }
}
