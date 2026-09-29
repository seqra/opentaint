package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FactTypeChecker.FilterResult
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.accept
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRSequentTaintUtil
import org.opentaint.dataflow.taint.DefaultFactWithMarkAfterAnyFieldResolver.Companion.createMarkAfterAccessorResolver
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.TaintSourceActionEvaluator
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JMethodExitExceptionalInst
import org.opentaint.jvm.graph.JMethodExitNormalInst
import org.opentaint.util.onSome

class JIRMethodSequentFlowFunction(
    private val apManager: ApManager,
    private val analysisContext: JIRMethodAnalysisContext,
    private val currentInst: JIRInst,
    private val generateTrace: Boolean,
): MethodSequentFlowFunction {
    private val factTypeChecker get() = analysisContext.factTypeChecker

    private val summary: JIRStatementSummary by lazy {
        JIRStatementSummary.build(apManager, currentInst, analysisContext.aliasAnalysis)
    }

    override fun propagateZeroToZero(): Set<Sequent> = buildSet {
        add(Sequent.ZeroToZero)

        if (currentInst is JIRAssignInst) {
            JIRMethodCallResolver.TypeInfoSequentFlowFunction.handle(analysisContext, currentInst) { accessors ->
                val lhv = accessPathBase(currentInst.lhv) ?: return@handle
                val startFact = apManager.createFinalAp(lhv, ExclusionSet.Universe)
                val fact = accessors.foldRight(startFact) { a, f -> f.prependAccessor(a) }
                add(Sequent.ZeroToFact(fact, TraceInfo.Flow))
            }
        }

        applyUnconditionalSources()
        applyUnconditionalSinks()
    }

    override fun propagateZeroToFact(currentFactAp: FinalFactAp) = buildSet {
        propagate(
            // todo: in trace mode we can't distinguish z2f from f2f
            initialFacts = emptySet<InitialFactAp>().takeIf { !generateTrace },
            factAp = currentFactAp,
            unchanged = { add(Sequent.Unchanged) },
            propagateTransferred = { fact, refinement ->
                check(refinement == null || refinement is ExclusionSet.Universe) {
                    "Zero to Fact edge can't be refined: $currentFactAp"
                }
                add(Sequent.ZeroToFact(fact, TraceInfo.Flow))
            },
            refineInitial = { },
            propagateFactWithRefinement = { refiner, fact, trace ->
                check(!refiner.hasRefinement) {
                    "Zero to Fact edge can't be refined: $currentFactAp"
                }
                add(Sequent.ZeroToFact(fact, trace))
            },
            sideEffect = { add(it) }
        )
    }

    override fun propagateFactToFact(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp
    ) = buildSet {
        propagate(
            initialFacts = setOf(initialFactAp),
            factAp = currentFactAp,
            unchanged = { add(Sequent.Unchanged) },
            propagateTransferred = { fact, refinement ->
                val initial = if (refinement == null) initialFactAp else initialFactAp.replaceExclusions(refinement)
                add(Sequent.FactToFact(initial, fact, TraceInfo.Flow))
            },
            refineInitial = { exclusion ->
                val refinedInitial = initialFactAp.replaceExclusions(exclusion)
                if (refinedInitial != initialFactAp) {
                    add(Sequent.SideEffectRequirement(refinedInitial))
                }
            },
            propagateFactWithRefinement = { refiner, fact, trace ->
                val refinedInitial = refiner.refineFact(initialFactAp)
                val refinedFact = refiner.refineFact(fact)
                add(Sequent.FactToFact(refinedInitial, refinedFact, trace))
            },
            sideEffect = { add(it) }
        )
    }

    override fun propagateNDFactToFact(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp
    ) = buildSet {
        propagate(
            initialFacts = initialFacts,
            factAp = currentFactAp,
            unchanged = { add(Sequent.Unchanged) },
            propagateTransferred = { fact, refinement ->
                check(refinement == null || refinement is ExclusionSet.Universe) {
                    "NDF2F edge can't be refined: $currentFactAp"
                }
                add(Sequent.NDFactToFact(initialFacts, fact, TraceInfo.Flow))
            },
            refineInitial = { },
            propagateFactWithRefinement = { refiner, fact, trace ->
                check(!refiner.hasRefinement) {
                    "NDF2F edge can't be refined: $currentFactAp"
                }
                add(Sequent.NDFactToFact(initialFacts, fact, trace))
            },
            sideEffect = { add(it) }
        )
    }

    private fun propagate(
        initialFacts: Set<InitialFactAp>?,
        factAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateTransferred: (FinalFactAp, ExclusionSet?) -> Unit,
        refineInitial: (ExclusionSet) -> Unit,
        propagateFactWithRefinement: (FactRefiner, FinalFactAp, TraceInfo) -> Unit,
        sideEffect: (Sequent.SideEffect) -> Unit
    ) {
        when (currentInst) {
            is JMethodExitNormalInst -> {
                propagateExitFact(
                    initialFacts, AccessPathBase.Return,
                    factAp, unchanged, propagateFactWithRefinement, sideEffect
                )
            }

            is JMethodExitExceptionalInst -> {
                propagateExitFact(
                    initialFacts, AccessPathBase.Exception,
                    factAp, unchanged, propagateFactWithRefinement, sideEffect
                )
            }

            else -> {
                if (!transfer(factAp, propagateTransferred, refineInitial)) {
                    unchanged()
                }
            }
        }
    }

    private fun transfer(
        factAp: FinalFactAp,
        emit: (FinalFactAp, ExclusionSet?) -> Unit,
        refine: (ExclusionSet) -> Unit
    ): Boolean {
        val edges = summary.edges[factAp.base] ?: return false

        var fact = factAp
        summary.typeFilters[fact.base]?.forEach { type ->
            fact = factTypeChecker.filterFactByLocalType(type, fact) ?: return true
        }

        for (edge in edges) {
            for (effect in MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge(fact, edge.from)) {
                val to = edge.to
                when (effect) {
                    is SummaryEdgeApplication.SummaryApRefinement -> {
                        if (to == null) continue
                        val result = to.concat(factTypeChecker, effect.delta) ?: continue
                        emit(result.replaceExclusions(fact.exclusions), null)
                    }

                    is SummaryEdgeApplication.SummaryExclusionRefinement -> {
                        if (to == null) {
                            refine(effect.exclusion)
                            continue
                        }
                        val result = to.concat(factTypeChecker, effect.delta) ?: continue
                        emit(result.replaceExclusions(effect.exclusion), effect.exclusion)
                    }
                }
            }
        }

        return true
    }

    private fun propagateExitFact(
        initialFacts: Set<InitialFactAp>?,
        exitBase: AccessPathBase,
        factAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFactWithRefinement: (FactRefiner, FinalFactAp, TraceInfo) -> Unit,
        sideEffect: (Sequent.SideEffect) -> Unit
    ) {
        val refiner = FactRefiner()
        val resultFacts = mutableListOf<Pair<FinalFactAp, TraceInfo>>()
        resultFacts += factAp to TraceInfo.Flow
        resultFacts += applyMethodExitSourceRules(exitBase, factAp, refiner)

        while (resultFacts.isNotEmpty()) {
            val (resultFact, factTrace) = resultFacts.removeLast()

            val (factsToDrop, newSources) = applyMethodExitSinkRules(exitBase, resultFact, initialFacts, sideEffect, refiner)
            resultFacts.addAll(newSources)

            val propagatedFact = resultFact.dropFinalFacts(factsToDrop)
                ?.dropArgumentsLocalTaintMarks(initialFacts != null && initialFacts.isEmpty())

            if (propagatedFact == factAp && !refiner.hasRefinement) {
                unchanged()
            } else if (propagatedFact != null) {
                propagateFactWithRefinement(refiner, propagatedFact, factTrace)
            }
        }

    }

    private fun applyMethodExitSinkRules(
        methodResult: AccessPathBase, fact: FinalFactAp,
        initialFacts: Set<InitialFactAp>?,
        sideEffect: (Sequent.SideEffect) -> Unit,
        refiner: FactRefiner
    ): Pair<List<InitialFactAp>, List<Pair<FinalFactAp, TraceInfo>>> = with(analysisContext.taint) {
        val sinkRules = sinkRulesForMethodExit(currentInst, fact, initialFacts).toList()
        if (sinkRules.isEmpty()) return emptyList<InitialFactAp>() to emptyList()

        val markAfterAnyFieldResolver = initialFacts?.let {
            createMarkAfterAccessorResolver(analysisContext.methodEntryPoint, it) { i, k ->
                sideEffect(Sequent.FactSideEffect(i, k))
            }
        }

        val taintUtil = JIRSequentTaintUtil(apManager, currentInst, analysisContext, generateTrace, methodResult)
        taintUtil.applySinkRules(sinkRules, FinalFactReader(fact, apManager), markAfterAnyFieldResolver)

        taintUtil.conditionReaders.forEach { refiner.add(it) }

        // todo: hack to drop global state var after exit sink
        val factsToDrop = taintUtil.allEvaluatedFacts.filter { it.base is AccessPathBase.ClassStatic }
        factsToDrop to taintUtil.factsAfterSink
    }

    private fun applyUnconditionalSinks() = with(analysisContext.taint) {
        if (currentInst !is JMethodExitNormalInst) return

        val sinkRules = sinkRulesForMethodExit(currentInst, fact = null, initialFacts = null).toList()
        sinkRules.forEach {
            if (it.condition.isTrue) {
                // todo: unconditional exit sink
            }
        }
    }

    private fun applyMethodExitSourceRules(
        methodResult: AccessPathBase, fact: FinalFactAp?, refiner: FactRefiner?,
    ): List<Pair<FinalFactAp, TraceInfo>> = with(analysisContext.taint) {
        val sourceRules = sourceRulesForMethodExit(currentInst, fact).toList()
        if (sourceRules.isEmpty()) return emptyList()

        val result = mutableListOf<Pair<FinalFactAp, TraceInfo>>()

        val taintUtil = JIRSequentTaintUtil(apManager, currentInst, analysisContext, generateTrace, methodResult)
        taintUtil.applySourceRules(
            sourceRules,
            initialFacts = emptySet(),
            factReader = fact?.let { FinalFactReader(it, apManager) },
            exclusion = fact?.exclusions ?: ExclusionSet.Universe,
            createFinalFact = { f, trace -> result.add(f to trace) },
            createEdge = { _, _, _ -> error("Unused operation") },
            createNDEdge = { _, _, _ -> error("Unused operation") }
        )

        refiner?.let { ref ->
            taintUtil.conditionReaders.forEach { ref.add(it) }
        }

        return result
    }

    private fun MutableSet<Sequent>.applyUnconditionalSources() {
        if (currentInst is JMethodExitNormalInst) {
            applyMethodExitSourceRules(AccessPathBase.Return, fact = null, refiner = null).forEach { (fact, trace) ->
                this += Sequent.ZeroToFact(fact, trace)
            }
        }

        if (currentInst !is JIRAssignInst) return

        val rhvFieldRef = currentInst.rhv as? JIRFieldRef ?: return
        val field = rhvFieldRef.field.field
        if (!field.isStatic) return

        val config = analysisContext.taint
        val sourceRules = config.sourceRulesForStaticField(field, currentInst, fact = null).toList()
        if (sourceRules.isEmpty()) return

        val lhv = accessPathBase(currentInst.lhv) ?: return

        val sourceEvaluator = TaintSourceActionEvaluator(
            apManager, ExclusionSet.Universe
        )

        for (sourceRuleWithCondition in sourceRules) {
            if (!sourceRuleWithCondition.condition.isTrue) continue

            val sourceRule = sourceRuleWithCondition.rule
            for (action in sourceRule.actionsAfter) {
                sourceEvaluator.accept(sourceRule, action).onSome { evaluatedFacts ->
                    val trace = TraceInfo.Rule(sourceRule, action)

                    evaluatedFacts.mapTo(this) {
                        if (it.base !is AccessPathBase.Return) {
                            TODO("Field source with non-result assign")
                        }

                        Sequent.ZeroToFact(it.rebase(lhv), trace)
                    }
                }
            }
        }
    }

    private fun FinalFactAp.dropFinalFacts(facts: List<InitialFactAp>): FinalFactAp? =
        facts.fold(this as FinalFactAp?) { acc, f -> acc?.dropFinalFact(f) }

    private fun FinalFactAp.dropFinalFact(fact: InitialFactAp): FinalFactAp? {
        if (base != fact.base) return this
        val res =  filterFact(FinalFactRemover(fact))
        return res
    }

    private class FinalFactRemover(val fact: InitialFactAp) : FactTypeChecker.FactApFilter {
        override fun check(accessor: Accessor): FilterResult {
            val nextFact = fact.readAccessor(accessor)
                ?: return FilterResult.Accept

            if (nextFact.startsWithAccessor(FinalAccessor)) {
                return FilterResult.FilterNext(FinalAccessorRemover)
            }

            return FilterResult.FilterNext(FinalFactRemover(nextFact))
        }
    }

    private object FinalAccessorRemover : FactTypeChecker.FactApFilter {
        override fun check(accessor: Accessor): FilterResult {
            if (accessor is FinalAccessor) return FilterResult.Reject
            return FilterResult.Accept
        }
    }

    // drop argument facts with tainted bases
    private fun FinalFactAp.dropArgumentsLocalTaintMarks(initialFactIsZero: Boolean): FinalFactAp? {
        if (!initialFactIsZero) return this
        if (base !is AccessPathBase.Argument && base !is AccessPathBase.This) return this
        return filterFact(TaintMarkRemover(analysisContext.taintMarksAssignedOnMethodEnter))
    }

    private class TaintMarkRemover(
        val marksToRemove: Set<TaintMarkAccessor>
    ) : FactTypeChecker.FactApFilter {
        override fun check(accessor: Accessor): FilterResult {
            if (accessor !is TaintMarkAccessor || accessor !in marksToRemove) return FilterResult.Accept
            return FilterResult.Reject
        }
    }

    private class FactRefiner {
        private var refinement: ExclusionSet = ExclusionSet.Empty
        val hasRefinement: Boolean get() = refinement !is ExclusionSet.Empty

        fun add(reader: FinalFactReader) {
            if (reader.hasRefinement) {
                refinement = refinement.union(reader.getRefinement())
            }
        }

        fun refineFact(factAp: InitialFactAp): InitialFactAp {
            if (!hasRefinement) return factAp
            return factAp.replaceExclusions(factAp.exclusions.union(refinement))
        }

        fun refineFact(factAp: FinalFactAp): FinalFactAp {
            if (!hasRefinement) return factAp
            return factAp.replaceExclusions(factAp.exclusions.union(refinement))
        }
    }
}
