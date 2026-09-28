package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodPositionBaseTypeResolver
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallRuleBasedSummaryRewriter
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintCleanActionEvaluator
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.hasAnyField
import org.opentaint.dataflow.taint.readPosition
import org.opentaint.dataflow.taint.withSuffix
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.ext.cfg.callExpr

class JIRBackwardSummaryRewriter(
    private val statement: JIRInst,
    private val analysisContext: JIRBackwardMethodAnalysisContext,
    private val apManager: ApManager,
) {
    private val rewriter by lazy {
        JIRMethodCallRuleBasedSummaryRewriter(statement, analysisContext, apManager)
    }

    private val cleanEvaluator by lazy {
        val callExpr = statement.callExpr ?: error("Call summary rewriter at statement without method call")
        JIRTaintCleanActionEvaluator(JIRMethodPositionBaseTypeResolver(callExpr.method.method))
    }

    fun rewriteDemand(fact: FinalFactAp): List<Pair<FinalFactAp, FinalFactReader>> =
        rewriter.rewriteSummaryFact(fact)

    fun rewriteSummary(edge: Edge.FactToFact): Edge.FactToFact? {
        val initial = edge.initialFactAp
        val actions = rewriter.removeMarkActions(initial.base)
        if (actions.isEmpty()) return edge

        var refinement: ExclusionSet = ExclusionSet.Empty
        for (action in actions) {
            val mark = TaintMarkAccessor(action.mark.name)
            for (position in cleanEvaluator.removeMarkPositions(action)) {
                val refinePosition = !position.hasAnyField()
                val present = readPosition(
                    ap = initial,
                    position = position.withSuffix(listOf(mark, FinalAccessor)),
                    onMismatch = { node: InitialFactAp, accessor ->
                        if (refinePosition && accessor != null && node.isAbstract()) {
                            refinement = refinement.add(accessor)
                        }
                        false
                    },
                    matchedNode = { true },
                )
                if (present) return null
            }
        }

        if (refinement is ExclusionSet.Empty) return edge

        return Edge.FactToFact(
            edge.methodEntryPoint,
            initial.replaceExclusions(initial.exclusions.union(refinement)),
            edge.statement,
            edge.factAp.replaceExclusions(edge.factAp.exclusions.union(refinement)),
        )
    }
}
