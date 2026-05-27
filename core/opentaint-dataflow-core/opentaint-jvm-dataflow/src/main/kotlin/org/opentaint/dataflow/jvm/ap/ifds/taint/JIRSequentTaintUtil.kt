package org.opentaint.dataflow.jvm.ap.ifds.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo.Rule
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker.VulnerabilityTriggerPosition
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.jvm.JirCondition
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSource
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.accept
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.TaintSourceActionEvaluator
import org.opentaint.dataflow.taint.TaintUtil
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.util.onSome

class JIRSequentTaintUtil(
    apManager: ApManager,
    val statement: JIRInst,
    val analysisContext: JIRMethodAnalysisContext,
    val generateTrace: Boolean,
    val methodResult: AccessPathBase,
) : TaintUtil<JirCondition, TaintMethodExitSource, TaintMethodExitSink, TraceInfo>(apManager) {
    private val sinkTracker get() = analysisContext.taint.taintSinkTracker

    override fun TaintMethodExitSource.srcCondition(): CommonCondition<JirCondition> = condition
    override fun TaintMethodExitSink.sinkCondition(): CommonCondition<JirCondition> = condition

    override fun sourceAssumptionsManager(): RuleAssumptionsManager<TaintMethodExitSource> =
        object : RuleAssumptionsManager<TaintMethodExitSource> {
            override fun storeAssumptions(
                rule: TaintMethodExitSource,
                assumptions: Map<InitialFactAp, Set<InitialFactAp>>
            ) = storeInfo {
                sinkTracker.addSourceRuleAssumptions(rule, statement, assumptions)
            }

            override fun currentAssumptions(rule: TaintMethodExitSource): Set<InitialFactAp> =
                sinkTracker.currentSourceRuleAssumptions(rule, statement)

            override fun currentAssumptionPreconditions(
                rule: TaintMethodExitSource,
                assumptions: List<InitialFactAp>
            ) = sinkTracker.currentSourceRuleAssumptionsPreconditions(rule, statement, assumptions)
        }

    override fun sinkAssumptionsManager(): RuleAssumptionsManager<TaintMethodExitSink> =
        object : RuleAssumptionsManager<TaintMethodExitSink> {
            override fun storeAssumptions(
                rule: TaintMethodExitSink,
                assumptions: Map<InitialFactAp, Set<InitialFactAp>>
            ) =
                storeInfo {
                    sinkTracker.addSinkRuleAssumptions(rule, statement, assumptions)
                }

            override fun currentAssumptions(rule: TaintMethodExitSink): Set<InitialFactAp> =
                sinkTracker.currentSinkRuleAssumptions(rule, statement)
        }

    val conditionReaders = mutableListOf<FinalFactReader>()

    override fun conditionFact(factReader: FinalFactReader): List<FinalFactReader> {
        val fact = factReader.factAp
        val resultFact = if (fact.base == methodResult) fact.rebase(AccessPathBase.Return) else fact
        val conditionReader = FinalFactReader(resultFact, apManager)
        conditionReaders.add(conditionReader)
        return listOf(conditionReader)
    }

    val allEvaluatedFacts = mutableListOf<InitialFactAp>()
    val factsAfterSink = mutableListOf<Pair<FinalFactAp, TraceInfo>>()

    override fun handleReachedSink(
        rule: TaintMethodExitSink,
        factReader: FinalFactReader?,
        rawEvaluatedFacts: List<InitialFactAp>
    ) {
        val evaluatedFacts = rawEvaluatedFacts.map {
            if (it.base == AccessPathBase.Return) it.rebase(methodResult) else it
        }

        allEvaluatedFacts += evaluatedFacts

        val taintSinkTracker = analysisContext.taint.taintSinkTracker

        if (rule.trackFactsReachAnalysisEnd.isEmpty()) {
            storeInfo {
                taintSinkTracker.addVulnerability(
                    analysisContext.methodEntryPoint, evaluatedFacts.toHashSet(),
                    statement, rule,
                    vulnerabilityTriggerPosition = VulnerabilityTriggerPosition.AFTER_INST
                )
            }

            return
        }

        val sourceEvaluator = TaintSourceActionEvaluator(
            apManager, ExclusionSet.Universe,
        )

        val requiredEndFacts = hashSetOf<FinalFactAp>()
        rule.trackFactsReachAnalysisEnd.forEach { action ->
            sourceEvaluator.accept(rule, action).onSome { facts ->
                facts.forEach { f ->
                    requiredEndFacts += f

                    val trace = Rule(rule, action)
                    factsAfterSink += f to trace
                }
            }
        }

        storeInfo {
            taintSinkTracker.addUnconditionalVulnerabilityWithEndFactRequirement(
                analysisContext.methodEntryPoint, statement, rule, requiredEndFacts
            )
        }
    }

    override fun applySourceAction(
        rule: TaintMethodExitSource,
        sourceEvaluator: TaintSourceActionEvaluator,

        createFinalFact: (FinalFactAp, TraceInfo) -> Unit
    ) {
        for (action in rule.actionsAfter) {
            sourceEvaluator.accept(rule, action).onSome { facts ->
                val trace = Rule(rule, action)
                facts.forEach { createFinalFact(it, trace) }
            }
        }
    }

    private inline fun storeInfo(body: () -> Unit) {
        if (generateTrace) return
        body()
    }
}
