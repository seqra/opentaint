package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.EdgeRefinement
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler.SummaryEdge
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.ir.api.jvm.cfg.JIRInst

class JIRBackwardMethodCallSummaryHandler(
    private val statement: JIRInst,
    private val analysisContext: JIRBackwardMethodAnalysisContext,
) : MethodCallSummaryHandler {
    override val factTypeChecker: FactTypeChecker get() = analysisContext.factTypeChecker

    override fun mapMethodExitToReturnFlowFact(fact: FinalFactAp): List<FinalFactAp> =
        JIRBackwardMethodCallFactMapper.mapMethodExitToReturnFlowFact(statement, fact, factTypeChecker)

    override fun handleSummary(
        currentFactAp: FinalFactAp,
        summaryEffect: EdgeRefinement,
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

            handleSummaryEdge(initialFactRefinement, summaryFactAp)
        }

        return result
    }
}
