package org.opentaint.dataflow.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPreconditionFact.CallFailurePreconditionFact
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition.PassRuleCondition
import org.opentaint.dataflow.taint.PreconditionCube
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr
import org.opentaint.dataflow.taint.preconditionDnf
import org.opentaint.ir.api.common.cfg.CommonInst

interface MethodCallPrecondition {
    sealed interface CallPrecondition {
        data object Unchanged : CallPrecondition
    }

    data class PreconditionFactsForInitialFact(
        val initialFact: InitialFactAp,
        val preconditionFacts: List<CallPreconditionFact>,
    ): CallPrecondition

    sealed interface CallPreconditionFact {
        sealed interface CallFailurePreconditionFact : CallPreconditionFact

        object UnresolvedCallSkip : CallPreconditionFact, CallFailurePreconditionFact
        data class CallToReturnTaintRule(val precondition: TaintRulePrecondition) : CallPreconditionFact, CallFailurePreconditionFact
        data class CallToStart(val callerFact: InitialFactAp, val startFactBase: AccessPathBase) : CallPreconditionFact
    }

    fun factPrecondition(fact: InitialFactAp): List<CallPrecondition>
    fun factPreconditionResolutionFailure(fact: InitialFactAp, startFactBase: AccessPathBase): List<CallFailurePreconditionFact>

    data class PassRuleConditionFacts(val facts: List<InitialFactAp>)

    fun resolvePassRuleCondition(precondition: PassRuleCondition, edges: MethodAnalyzerEdges): List<PassRuleConditionFacts>

    interface Default: MethodCallPrecondition {
        val apManager: ApManager

        fun mapExit2Return(fact: InitialFactAp): List<InitialFactAp>

        override fun resolvePassRuleCondition(
            precondition: PassRuleCondition,
            edges: MethodAnalyzerEdges
        ): List<PassRuleConditionFacts> = when (precondition) {
            is PassRuleCondition.Fact -> {
                listOf(PassRuleConditionFacts(listOf(precondition.fact)))
            }

            is PassRuleCondition.Expr -> {
                precondition.expr.preconditionDnf(edges).map { PassRuleConditionFacts(it.facts.toList()) }
            }

            is PassRuleCondition.FactWithExpr -> {
                precondition.expr.preconditionDnf(edges).map {
                    val allFacts = it.facts + precondition.fact
                    PassRuleConditionFacts(allFacts.toList())
                }
            }
        }

        fun allStatements(): List<CommonInst>

        fun allRelevantFacts(edges: MethodAnalyzerEdges, startsWith: InitialFactAp): List<FinalFactAp> {
            val facts = mutableListOf<FinalFactAp>()
            allStatements().forEach { stmt ->
                facts += edges.allZeroToFactFactsAtStatement(stmt, startsWith)
                edges.allFactToFactFactsAtStatement(stmt, startsWith).mapTo(facts) { it.second }
                edges.allNDFactToFactFactsAtStatement(stmt, startsWith).mapTo(facts) { it.second }

            }
            return facts
        }

        fun TaintMarkAwareConditionExpr.preconditionDnf(edges: MethodAnalyzerEdges): List<PreconditionCube> =
            preconditionDnf(apManager, { allRelevantFacts(edges, it) }) { mapExit2Return(it) }
    }
}
