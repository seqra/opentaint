package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoMethodCallFactMapper
import org.opentaint.dataflow.go.GoMethodCallFactMapper.mapMethodExitToReturnFlowFact
import org.opentaint.dataflow.go.rules.GoRuleCondition
import org.opentaint.dataflow.go.rules.TaintRules
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.TaintSourceActionEvaluator
import org.opentaint.dataflow.taint.TaintUtil
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRValue
import org.opentaint.util.onSome

class GoMethodCallTaintUtil(
    private val statement: GoIRInst,
    private val callExpr: GoCallExpr,
    val returnValue: GoIRValue?,
    private val context: GoMethodAnalysisContext,
    apManager: ApManager
) : TaintUtil<GoRuleCondition, TaintRules.Source, TaintRules.Sink, TraceInfo>(apManager) {
    override fun TaintRules.Source.srcCondition(): CommonCondition<GoRuleCondition> = mkTrue()
    override fun TaintRules.Sink.sinkCondition(): CommonCondition<GoRuleCondition> = condition

    override fun sourceAssumptionsManager(): RuleAssumptionsManager<TaintRules.Source> =
        object : RuleAssumptionsManager<TaintRules.Source> {
            override fun storeAssumptions(
                rule: TaintRules.Source,
                assumptions: Map<InitialFactAp, Set<InitialFactAp>>
            ) {
                TODO("Rule assumptions")
            }

            override fun currentAssumptions(rule: TaintRules.Source): Set<InitialFactAp> {
                TODO("Rule assumptions")
            }
        }

    override fun sinkAssumptionsManager(): RuleAssumptionsManager<TaintRules.Sink> =
        object : RuleAssumptionsManager<TaintRules.Sink> {
            override fun storeAssumptions(
                rule: TaintRules.Sink,
                assumptions: Map<InitialFactAp, Set<InitialFactAp>>
            ) {
                TODO("Rule assumptions")
            }

            override fun currentAssumptions(rule: TaintRules.Sink): Set<InitialFactAp> {
                TODO("Rule assumptions")
            }
        }

    override fun conditionFact(factReader: FinalFactReader): List<FinalFactReader> {
        val readers = mutableListOf<FinalFactReader>()
        GoMethodCallFactMapper.mapMethodCallToStartFlowFact(
            statement,
            callee = callExpr.enclosingMethod, // todo: remove hack
            callExpr,
            returnValue,
            factReader.factAp,
            FactTypeChecker.Dummy
        ) { fact, startBase ->
            readers += FinalFactReader(fact.rebase(startBase), apManager)
        }
        return readers
    }

    override fun handleReachedSink(
        rule: TaintRules.Sink,
        factReader: FinalFactReader?,
        evaluatedFacts: List<InitialFactAp>
    ) {
        val callerFacts = evaluatedFacts.mapTo(hashSetOf()) {
            mapMethodExitToReturnFlowFact(statement, it).single()
        }

        context.taint.taintSinkTracker.addVulnerability(
            methodEntryPoint = context.methodEntryPoint,
            statement = statement,
            facts = callerFacts,
            rule = rule,
        )
    }

    override fun applySourceAction(
        rule: TaintRules.Source,
        sourceEvaluator: TaintSourceActionEvaluator,
        createFinalFact: (FinalFactAp, TraceInfo) -> Unit
    ) {
        val position = GoFlowFunctionUtils.resolvePositionAccess(rule.pos)
        sourceEvaluator.evaluate(rule, rule, position, TaintMarkAccessor(rule.mark)).onSome { facts ->
            facts.forEach { f ->
                val callerFacts = mapMethodExitToReturnFlowFact(statement, f, FactTypeChecker.Dummy)
                callerFacts.forEach { createFinalFact(it, TraceInfo.Flow) }
            }
        }
    }
}
