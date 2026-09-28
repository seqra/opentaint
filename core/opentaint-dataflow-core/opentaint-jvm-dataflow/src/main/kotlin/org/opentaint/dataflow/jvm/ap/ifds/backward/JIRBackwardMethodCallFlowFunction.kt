package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToStartZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.Drop
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.ZeroCallFact
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.configuration.TaintCleanReach
import org.opentaint.dataflow.configuration.jvm.PositionAccessor
import org.opentaint.dataflow.configuration.jvm.PositionWithAccess
import org.opentaint.dataflow.configuration.jvm.RemoveMark
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.configuration.jvm.serialized.UserDefinedRuleInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.analysis.apAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodPositionBaseTypeResolver
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.accept
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.applyCleaner
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintCleanActionEvaluator
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.jvm.util.callee
import org.opentaint.dataflow.taint.EvaluatedPass
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.TaintFactAwareConditionEvaluator
import org.opentaint.dataflow.taint.TaintPassActionInverseEvaluator
import org.opentaint.ir.api.jvm.JIRType
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRInstanceCallExpr
import org.opentaint.jvm.graph.JMethodEnterInst
import org.opentaint.util.onSome

class JIRBackwardMethodCallFlowFunction(
    private val apManager: ApManager,
    private val analysisContext: JIRBackwardMethodAnalysisContext,
    private val returnValue: JIRImmediate?,
    private val callExpr: JIRCallExpr,
    private val statement: JIRInst,
) : MethodCallFlowFunction.Default {
    private val rules by lazy { JIRBackwardTaintRules(apManager, analysisContext) }

    private val taintCtx get() = analysisContext.taint

    private val summaryRewriter by lazy {
        JIRBackwardSummaryRewriter(statement, analysisContext, apManager)
    }

    private val typeResolver by lazy {
        JIRMethodPositionBaseTypeResolver(callExpr.method.method)
    }

    override fun propagateZeroToZero(): Set<ZeroCallFact> = buildSet {
        add(CallToReturnZeroFact)
        add(CallToStartZeroFact)
        rules.registerPrescanCallSources(statement, callExpr, returnValue)

        val demands = rules.callSinkDemands(statement, callExpr, returnValue)
        rules.recordSinkDemands(statement, demands).forEach { seed ->
            add(CallToReturnZFact(seed, TraceInfo.Flow))
        }
    }

    override fun propagateFact(
        initialFacts: Set<InitialFactAp>,
        exclusion: ExclusionSet,
        factAp: FinalFactAp,
        skipCall: () -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo) -> Unit,
        addCallToStart: (factReader: FinalFactReader, callerFact: FinalFactAp, startFactBase: AccessPathBase, TraceInfo) -> Unit,
        addUnchecked: (MethodCallFlowFunction.CallFact) -> Unit,
    ) {
        val factReader = FinalFactReader(factAp, apManager)
        rules.matchEndRequirement(statement, factAp)?.let { factReader.updateRefinement(it) }

        val demands = mutableListOf<FinalFactAp>()

        if (JIRBackwardMethodCallFactMapper.factIsRelevantToMethodCall(statement, returnValue, callExpr, factAp)) {
            demands += factAp
        } else {
            skipCall()
        }

        demands += callSiteAliasDemands(factReader)

        val conditionDemands = mutableListOf<FinalFactAp>()

        for (demand in demands) {
            JIRBackwardMethodCallFactMapper.mapMethodCallToStartFlowFact(
                statement,
                callee = callExpr.callee,
                callExpr = callExpr,
                returnValue = returnValue,
                factAp = demand,
                checker = analysisContext.factTypeChecker,
            ) { callerFact, startFactBase ->
                val sourceMatches = rules.matchCallSources(statement, callExpr, returnValue, callerFact, startFactBase)
                rules.recordSourceMatches(statement, sourceMatches)
                sourceMatches.reader?.let { factReader.updateRefinement(it) }
                conditionDemands += sourceMatches.conditionDemands

                applyCleanersOrCallToStart(
                    factReader, callerFact, startFactBase,
                    addCallToReturn, addCallToStart, addUnchecked
                )
            }
        }

        for (demand in conditionDemands) {
            addCallToReturn(factReader, demand, TraceInfo.Flow)
        }

        if (factReader.hasRefinement) {
            addSideEffectRequirement(factReader)
        }
    }

    private fun callSiteAliasDemands(factReader: FinalFactReader): List<FinalFactAp> {
        val aliasAnalysis = analysisContext.aliasAnalysis ?: return emptyList()
        val factAp = factReader.factAp

        val result = mutableListOf<FinalFactAp>()
        for (local in callLocals) {
            val aliasesBefore = aliasAnalysis.findAlias(local, statement) ?: continue
            val aliasesAfter = aliasAnalysis.findAliasAfterStatement(local, statement)?.toSet() ?: continue

            for (alias in aliasesBefore) {
                if (alias !is AliasApInfo || alias.base != factAp.base || alias !in aliasesAfter) continue
                if (alias.accessors.isEmpty() && local == factAp.base) continue

                val accessors = alias.accessors.map { it.apAccessor() }
                val position = accessors.fold(PositionAccess.Simple(factAp.base) as PositionAccess) { position, accessor ->
                    PositionAccess.Complex(position, accessor)
                }
                if (!factReader.containsPosition(position)) continue

                val aliased = accessors.fold(factAp as FinalFactAp?) { fact, accessor -> fact?.readAccessor(accessor) }
                    ?: continue
                result += aliased.rebase(local)
            }
        }
        return result
    }

    private val callLocals: List<AccessPathBase.LocalVar> by lazy {
        buildList {
            (callExpr as? JIRInstanceCallExpr)?.let { add(it.instance) }
            addAll(callExpr.args)
            returnValue?.let { add(it) }
        }.mapNotNull { MethodFlowFunctionUtils.accessPathBase(it) as? AccessPathBase.LocalVar }.distinct()
    }

    private fun applyCleanersOrCallToStart(
        originalFactReader: FinalFactReader,
        unmappedCallerFactAp: FinalFactAp,
        startFactBase: AccessPathBase,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo) -> Unit,
        addCallToStart: (factReader: FinalFactReader, callerFactAp: FinalFactAp, startFactBase: AccessPathBase, TraceInfo) -> Unit,
        addUnchecked: (MethodCallFlowFunction.CallFact) -> Unit,
    ) {
        val calleeFact = unmappedCallerFactAp.rebase(startFactBase)
        val survivingFacts = applyCleaners(originalFactReader, calleeFact) { trace ->
            addUnchecked(Drop(trace))
        }

        for (factReaderAfterCleaner in survivingFacts) {
            originalFactReader.updateRefinement(factReaderAfterCleaner)

            val cleanedFact = factReaderAfterCleaner.factAp
            check(cleanedFact.base == startFactBase)

            val unmappedFact = cleanedFact.rebase(unmappedCallerFactAp.base)

            if (callExpr.callee.isConstructor) {
                addCallToReturn(originalFactReader, unmappedFact, TraceInfo.Flow)
            }

            addCallToStart(originalFactReader, unmappedFact, startFactBase, TraceInfo.Flow)
        }
    }

    private inline fun applyCleaners(
        refinementReader: FinalFactReader,
        calleeFact: FinalFactAp,
        onDrop: (TraceInfo?) -> Unit,
    ): List<FinalFactReader> {
        val conditionFactReader = FinalFactReader(calleeFact, apManager)
        val conditionEvaluator = TaintFactAwareConditionEvaluator(
            listOf(conditionFactReader),
            markAfterAnyAccessorResolver = null
        )

        val cleanRules = taintCtx.cleanRulesForCallStatement(statement, callExpr, returnValue, calleeFact)
        val actionEvaluator = JIRTaintCleanActionEvaluator(typeResolver)
        val cleanerResults = cleanerInputs(calleeFact, cleanRules, conditionEvaluator).flatMap { fact ->
            applyCleaner(cleanRules, FinalFactReader(fact, apManager), conditionEvaluator, actionEvaluator)
        }

        refinementReader.updateRefinement(conditionFactReader)

        val survivingFacts = mutableListOf<FinalFactReader>()
        for (cleanerResult in cleanerResults) {
            val factReaderAfterCleaner = cleanerResult.fact
            if (factReaderAfterCleaner != null) {
                survivingFacts += factReaderAfterCleaner
                continue
            }

            val trace = cleanerResult.action
                ?.takeIf { (it.rule as? TaintConfigurationItem)?.info is UserDefinedRuleInfo }
                ?.let { TraceInfo.Rule(it.rule, it.action) }
            onDrop(trace)
        }
        return survivingFacts
    }

    private fun cleanerInputs(
        calleeFact: FinalFactAp,
        cleanRules: List<RuleWithCondition<TaintCleaner>>,
        conditionEvaluator: TaintFactAwareConditionEvaluator,
    ): List<FinalFactAp> {
        val marks = starRootMarksRemoved(calleeFact, cleanRules, conditionEvaluator)
        if (marks.isEmpty() || marks.any { it in methodEntryAnyFieldMarks }) return listOf(calleeFact)
        return analysisContext.starUnroller.unroll(calleeFact, calleeBaseType(calleeFact.base)) ?: listOf(calleeFact)
    }

    private fun starRootMarksRemoved(
        calleeFact: FinalFactAp,
        cleanRules: List<RuleWithCondition<TaintCleaner>>,
        conditionEvaluator: TaintFactAwareConditionEvaluator,
    ): Set<TaintMarkAccessor> {
        if (!calleeFact.startsWithAccessor(AnyAccessor)) return emptySet()
        val star = calleeFact.readAccessor(AnyAccessor) ?: return emptySet()
        val root = PositionAccess.Simple(calleeFact.base)

        val marks = hashSetOf<TaintMarkAccessor>()
        for (ruleWithCondition in cleanRules) {
            val ruleMarks = ruleWithCondition.rule.actionsAfter.mapNotNull { action ->
                if (action !is RemoveMark || action.reach != TaintCleanReach.Exact) return@mapNotNull null
                if (action.position.resolveAp() != root) return@mapNotNull null
                TaintMarkAccessor(action.mark.name).takeIf { star.startsWithAccessor(it) }
            }
            if (ruleMarks.isNotEmpty() && ruleWithCondition.isApplicable(conditionEvaluator)) {
                marks += ruleMarks
            }
        }
        return marks
    }

    private val methodEntryAnyFieldMarks: Set<TaintMarkAccessor> by lazy {
        val enter = analysisContext.forwardEntryPoint as? JMethodEnterInst ?: return@lazy emptySet()
        taintCtx.sourceRulesForMethodEntry(enter, fact = null)
            .filter { !it.condition.isFalse }
            .flatMapTo(hashSetOf()) { ruleWithCondition ->
                ruleWithCondition.rule.actionsAfter
                    .filter { (it.position as? PositionWithAccess)?.access == PositionAccessor.AnyFieldAccessor }
                    .map { TaintMarkAccessor(it.mark.name) }
            }
    }

    private fun RuleWithCondition<TaintCleaner>.isApplicable(conditionEvaluator: TaintFactAwareConditionEvaluator): Boolean =
        when {
            condition.isFalse -> false
            condition.isTrue -> true
            else -> conditionEvaluator.evalWithAssumptionsCheck(condition.expr)
        }

    private fun calleeBaseType(base: AccessPathBase): JIRType? = when (base) {
        is AccessPathBase.Return -> returnValue?.type
        is AccessPathBase.This -> (callExpr as? JIRInstanceCallExpr)?.instance?.type
        is AccessPathBase.Argument -> callExpr.args.getOrNull(base.idx)?.type
        else -> null
    }

    override fun propagateUnresolvedCallFact(
        factAp: FinalFactAp,
        startFactBase: AccessPathBase,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo?) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
    ) {
        if (startFactBase != AccessPathBase.Return) {
            for ((keptFact, keptReader) in summaryRewriter.rewriteDemand(factAp)) {
                addCallToReturn(keptReader, keptReader.refineFact(keptFact), null)
            }
        }

        val factReader = FinalFactReader(factAp, apManager)
        val calleeFact = factAp.rebase(startFactBase)

        val passRules = taintCtx.passRulesForCallStatement(statement, callExpr, returnValue, calleeFact)
            .toMutableList()

        analysisContext.analysisManager.params.defaultGetModel?.run {
            passRules += defaultPropagationRules(callExpr.callee)
        }

        for ((demand, rewriteReader) in summaryRewriter.rewriteDemand(calleeFact)) {
            val passFactReader = FinalFactReader(rewriteReader.refineFact(demand), apManager)
            passFactReader.updateRefinement(rewriteReader)

            val passEvaluator = TaintPassActionInverseEvaluator(
                apManager, analysisContext.factTypeChecker, passFactReader, typeResolver
            )

            for (evaluatedPass in applyInversePassThrough(passRules, passEvaluator)) {
                val survivingFacts = applyCleaners(passFactReader, evaluatedPass.fact) { }
                for (factReaderAfterCleaner in survivingFacts) {
                    passFactReader.updateRefinement(factReaderAfterCleaner)

                    val mappedFact = rules.mapCalleeToCaller(statement, factReaderAfterCleaner.factAp) ?: continue
                    val trace = TraceInfo.Rule(evaluatedPass.rule, evaluatedPass.action)
                    addCallToReturn(passFactReader, mappedFact, trace)
                }
            }

            factReader.updateRefinement(passFactReader)
        }

        if (factReader.hasRefinement) {
            addSideEffectRequirement(factReader)
        }
    }

    private fun applyInversePassThrough(
        passRules: List<RuleWithCondition<TaintPassThrough>>,
        passEvaluator: TaintPassActionInverseEvaluator,
    ): List<EvaluatedPass> {
        val result = mutableListOf<EvaluatedPass>()
        for (ruleWithCondition in passRules) {
            if (ruleWithCondition.condition.isFalse) continue

            val rule = ruleWithCondition.rule
            for (action in rule.actionsAfter) {
                passEvaluator.accept(rule, action).onSome { result += it }
            }
        }
        return result
    }
}
