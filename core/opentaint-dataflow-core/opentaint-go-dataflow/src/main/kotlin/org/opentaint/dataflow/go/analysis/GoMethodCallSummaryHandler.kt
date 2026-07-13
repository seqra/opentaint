package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler.SummaryEdge
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoLanguageManager
import org.opentaint.dataflow.go.GoMethodCallFactMapper
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRValue

class GoMethodCallSummaryHandler(
    private val languageManager: GoLanguageManager,
    private val apManager: ApManager,
    private val context: GoMethodAnalysisContext,
    private val statement: GoIRInst,
) : MethodCallSummaryHandler {
    override val factTypeChecker: FactTypeChecker = FactTypeChecker.Dummy

    override fun mapMethodExitToReturnFlowFact(fact: FinalFactAp): List<FinalFactAp> {
        return GoMethodCallFactMapper.mapMethodExitToReturnFlowFact(statement, fact, factTypeChecker)
    }

    private val callExpr: GoCallExpr by lazy {
        languageManager.getCallExpr(statement) as? GoCallExpr
            ?: error("No call expr found for statement $statement")
    }

    private val returnValue: GoIRValue?
        get() = GoFlowFunctionUtils.extractResultRegister(statement)

    private val summaryRewriter by lazy {
        GoCallRuleBasedSummaryRewriter(statement, callExpr, returnValue, context, apManager)
    }

    override fun prepareFactToFactSummary(summaryEdge: Edge.FactToFact): List<Edge.FactToFact> =
        summaryRewriter.rewriteSummaryFact(summaryEdge.factAp).map { (resultFact, refinement) ->
            Edge.FactToFact(
                summaryEdge.methodEntryPoint,
                refinement.refineFact(summaryEdge.initialFactAp),
                summaryEdge.statement,
                refinement.refineFact(resultFact)
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

    override fun handleZeroToZero(summaryFact: FinalFactAp?): Set<Sequent> =
        super.handleZeroToZero(summaryFact).flatMapTo(hashSetOf()) { seq ->
            if (seq !is Sequent.ZeroToFact) return@flatMapTo listOf(seq)

            val result = mutableListOf(seq)
            applyCallAliases(seq.factAp) { aliased ->
                result += Sequent.ZeroToFact(aliased, seq.traceInfo)
            }
            result
        }

    override fun handleSummary(
        currentFactAp: FinalFactAp,
        summaryEffect: SummaryEdgeApplication,
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
                applyCallAliases(summaryFactAp) { aliased ->
                    result += handleSummaryEdge(initialFactRefinement, aliased)
                }
            }

            handleSummaryEdge(initialFactRefinement, summaryFactAp)
        }

        return result
    }

    private fun applyCallAliases(fact: FinalFactAp, body: (FinalFactAp) -> Unit) {
        context.aliasAnalysis.forEachHeapAliasAtStatement(statement, fact) {
            body(it)
        }
    }

    private fun SummaryEdge.hasMemoryEffect(): Boolean {
        if (this !is SummaryEdge.F2F) return true
        return !final.equalTo(initial)
    }
}
