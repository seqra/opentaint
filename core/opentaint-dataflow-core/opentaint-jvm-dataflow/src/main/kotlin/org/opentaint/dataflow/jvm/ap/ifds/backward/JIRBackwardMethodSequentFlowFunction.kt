package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.configuration.jvm.Condition
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodSequentFlowFunction
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodSequentFlowFunction.FactRefiner
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRStatementSummary
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardTaintAnalysisContext.Companion.positiveMarks
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRSequentTaintUtil
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JMethodEnterInst
import org.opentaint.jvm.graph.JMethodExitExceptionalInst
import org.opentaint.jvm.graph.JMethodExitNormalInst

class JIRBackwardMethodSequentFlowFunction(
    private val apManager: ApManager,
    private val analysisContext: JIRMethodAnalysisContext,
    private val taint: JIRBackwardTaintAnalysisContext,
    private val currentInst: JIRInst,
) : MethodSequentFlowFunction {
    private val forward = JIRMethodSequentFlowFunction(apManager, analysisContext, currentInst, generateTrace = false)

    private val summary: StatementSummary by lazy {
        JIRStatementSummary.buildReversed(apManager, currentInst, analysisContext.aliasAnalysis)
    }

    override fun propagateZeroToZero(): Set<Sequent> = buildSet {
        add(Sequent.ZeroToZero)

        when (currentInst) {
            is JMethodExitNormalInst -> {
                for ((fact, _) in forward.applyMethodExitSourceRules(AccessPathBase.Return, fact = null, refiner = null)) {
                    add(Sequent.ZeroToFact(fact, TraceInfo.Flow))
                }
                applyUnconditionalExitSinks(AccessPathBase.Return)
            }

            is JMethodExitExceptionalInst -> applyUnconditionalExitSinks(AccessPathBase.Exception)

            is JMethodEnterInst -> {
                sinkUtil<TaintMethodEntrySink>(AccessPathBase.Return)
                    .applySinkRules(entrySinkRules(currentInst), factReader = null, markAfterAnyFieldResolver = null)
                applySourceRules(entrySourceRules(currentInst), AccessPathBase.Return, fact = null, refiner = null)
                    .forEach { add(Sequent.ZeroToFact(it, TraceInfo.Flow)) }
            }
        }
    }

    override fun propagateZeroToFact(currentFactAp: FinalFactAp) = buildSet {
        propagate(
            initialFacts = emptySet(),
            factAp = currentFactAp,
            propagateFact = { fact ->
                check(fact.exclusions is ExclusionSet.Universe) {
                    "Zero to Fact edge can't be refined: $currentFactAp"
                }
                add(Sequent.ZeroToFact(fact, TraceInfo.Flow))
            },
            refineInitial = { },
        )
    }

    override fun propagateFactToFact(initialFactAp: InitialFactAp, currentFactAp: FinalFactAp) = buildSet {
        propagate(
            initialFacts = setOf(initialFactAp),
            factAp = currentFactAp,
            propagateFact = { fact ->
                if (fact.exclusions is ExclusionSet.Universe) {
                    add(Sequent.ZeroToFact(fact, TraceInfo.Flow))
                } else {
                    add(Sequent.FactToFact(initialFactAp.replaceExclusions(fact.exclusions), fact, TraceInfo.Flow))
                }
            },
            refineInitial = { exclusions ->
                val refinedInitial = initialFactAp.replaceExclusions(exclusions)
                if (refinedInitial != initialFactAp) {
                    add(Sequent.SideEffectRequirement(refinedInitial))
                }
            },
        )
    }

    override fun propagateNDFactToFact(initialFacts: Set<InitialFactAp>, currentFactAp: FinalFactAp) = buildSet {
        propagate(
            initialFacts = initialFacts,
            factAp = currentFactAp,
            propagateFact = { fact ->
                check(fact.exclusions is ExclusionSet.Universe) {
                    "NDF2F edge can't be refined: $currentFactAp"
                }
                add(Sequent.NDFactToFact(initialFacts, fact, TraceInfo.Flow))
            },
            refineInitial = { },
        )
    }

    private fun MutableSet<Sequent>.propagate(
        initialFacts: Set<InitialFactAp>,
        factAp: FinalFactAp,
        propagateFact: (FinalFactAp) -> Unit,
        refineInitial: (ExclusionSet) -> Unit,
    ) {
        val refiner = FactRefiner()
        val demands = mutableListOf<FinalFactAp>()

        when (currentInst) {
            is JMethodExitNormalInst -> propagateExitFact(AccessPathBase.Return, initialFacts, factAp, refiner, demands)
            is JMethodExitExceptionalInst -> propagateExitFact(AccessPathBase.Exception, initialFacts, factAp, refiner, demands)
            is JMethodEnterInst -> propagateEnterFact(currentInst, initialFacts, factAp, refiner, demands)

            else -> {
                if (currentInst is JIRAssignInst) {
                    applyStaticFieldRules(currentInst, factAp, refiner, demands)
                }

                if (!refiner.hasRefinement && demands.isEmpty()) {
                    if (!transfer(summary, factAp, analysisContext.factTypeChecker, propagateFact, refineInitial)) {
                        add(Sequent.Unchanged)
                    }
                    return
                }

                if (!transfer(summary, factAp, analysisContext.factTypeChecker, demands::add, refineInitial)) {
                    demands += factAp
                }
            }
        }

        for (demand in demands) {
            if (demand == factAp && !refiner.hasRefinement) {
                add(Sequent.Unchanged)
            } else {
                propagateFact(refiner.refineFact(demand))
            }
        }
    }

    private fun MutableSet<Sequent>.propagateExitFact(
        exitBase: AccessPathBase,
        initialFacts: Set<InitialFactAp>,
        factAp: FinalFactAp,
        refiner: FactRefiner,
        demands: MutableList<FinalFactAp>,
    ) {
        forward.applyMethodExitSinkRules(exitBase, factAp, initialFacts, sideEffect = { add(it) }, refiner)
        demands += factAp
        forward.applyMethodExitSourceRules(exitBase, factAp, refiner).mapTo(demands) { it.first }
    }

    private fun propagateEnterFact(
        inst: JMethodEnterInst,
        initialFacts: Set<InitialFactAp>,
        factAp: FinalFactAp,
        refiner: FactRefiner,
        demands: MutableList<FinalFactAp>,
    ) {
        val sinks = entrySinkRules(inst)
        val sources = entrySourceRules(inst)
        val conditions = sinks.map { it.rule.condition } + sources.map { it.rule.condition }
        if (!leavesThroughArgumentRoot(conditions, initialFacts)) {
            val util = sinkUtil<TaintMethodEntrySink>(AccessPathBase.Return)
            util.applySinkRules(sinks, FinalFactReader(factAp, apManager), markAfterAnyFieldResolver = null)
            util.conditionReaders.forEach(refiner::add)
            demands += applySourceRules(sources, AccessPathBase.Return, factAp, refiner)
        }

        demands += factAp
    }

    private fun applyUnconditionalExitSinks(methodResult: AccessPathBase) {
        val rules = taint.sinkRulesForMethodExit(currentInst, fact = null, initialFacts = emptySet())
        sinkUtil<TaintMethodExitSink>(methodResult).applySinkRules(rules, factReader = null, markAfterAnyFieldResolver = null)
    }

    private fun <Sink : TaintConfigurationSink> sinkUtil(methodResult: AccessPathBase) =
        JIRSequentTaintUtil<TaintConfigurationSource, Sink>(
            apManager, currentInst, analysisContext, generateTrace = false, methodResult
        )

    private fun entrySinkRules(inst: JIRInst): List<RuleWithCondition<TaintMethodEntrySink>> =
        taint.sinkRulesForMethodEntry(inst, fact = null)

    private fun entrySourceRules(inst: JIRInst): List<RuleWithCondition<TaintEntryPointSource>> =
        taint.sourceRulesForMethodEntry(inst, fact = null)

    private fun <Source : TaintConfigurationSource> applySourceRules(
        rules: List<RuleWithCondition<Source>>,
        methodResult: AccessPathBase,
        fact: FinalFactAp?,
        refiner: FactRefiner?,
    ): List<FinalFactAp> {
        if (rules.isEmpty()) return emptyList()

        val result = mutableListOf<FinalFactAp>()
        val util = JIRSequentTaintUtil<Source, TaintConfigurationSink>(
            apManager, currentInst, analysisContext, generateTrace = false, methodResult
        )
        util.applySourceRules(
            rules,
            initialFacts = emptySet(),
            factReader = fact?.let { FinalFactReader(it, apManager) },
            exclusion = fact?.exclusions ?: ExclusionSet.Universe,
            createFinalFact = { f, _ -> result += f },
            createEdge = { _, _, _ -> error("Unused operation") },
            createNDEdge = { _, _, _ -> error("Unused operation") }
        )
        refiner?.let { util.conditionReaders.forEach(it::add) }
        return result
    }

    private fun applyStaticFieldRules(
        inst: JIRAssignInst,
        fact: FinalFactAp,
        refiner: FactRefiner,
        demands: MutableList<FinalFactAp>,
    ) {
        val field = (inst.rhv as? JIRFieldRef)?.field?.field?.takeIf { it.isStatic } ?: return
        val lhv = accessPathBase(inst.lhv) ?: return
        if (fact.base != lhv) return

        val sinks = taint.sinkRulesForStaticField(field, inst)
        val sources = taint.sourceRulesForStaticField(field, inst, fact = null)
        if (sinks.isEmpty() && sources.isEmpty()) return

        val util = sinkUtil<TaintMethodSink>(lhv)
        util.applySinkRules(sinks, FinalFactReader(fact, apManager), markAfterAnyFieldResolver = null)
        util.conditionReaders.forEach(refiner::add)

        demands += applySourceRules(sources, lhv, fact, refiner)
    }

    private fun leavesThroughArgumentRoot(
        conditions: List<Condition>,
        initialFacts: Set<InitialFactAp>,
    ): Boolean {
        if (initialFacts.isEmpty()) return false

        val marks = conditions.flatMapTo(hashSetOf()) { condition ->
            condition.positiveMarks().map { TaintMarkAccessor(it.mark.name) }
        }
        return initialFacts.all { initialFact ->
            val base = initialFact.base
            (base is AccessPathBase.Argument || base is AccessPathBase.This) &&
                marks.any { initialFact.startsWithAccessor(it) }
        }
    }
}
