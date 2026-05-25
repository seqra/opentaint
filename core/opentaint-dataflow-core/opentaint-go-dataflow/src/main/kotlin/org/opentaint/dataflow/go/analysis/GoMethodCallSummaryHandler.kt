package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
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
}
