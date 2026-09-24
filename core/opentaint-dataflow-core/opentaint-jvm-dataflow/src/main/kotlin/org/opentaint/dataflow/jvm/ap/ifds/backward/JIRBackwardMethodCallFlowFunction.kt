package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnFFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnNonDistributiveFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToStartZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.Drop
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.FactCallFailureFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.SideEffectRequirement
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.ZeroCallFact
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
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
import org.opentaint.dataflow.jvm.util.callee
import org.opentaint.dataflow.taint.EvaluatedPass
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.TaintFactAwareConditionEvaluator
import org.opentaint.dataflow.taint.TaintPassActionInverseEvaluator
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRInstanceCallExpr
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

    private val typeResolver by lazy {
        JIRMethodPositionBaseTypeResolver(callExpr.method.method)
    }

    override fun propagateZeroToZero(): Set<ZeroCallFact> = buildSet {
        add(CallToReturnZeroFact)
        add(CallToStartZeroFact)

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
        if (factAp.base !is AccessPathBase.LocalVar) return emptyList()

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
        val cleanerResults = applyCleaner(
            cleanRules,
            FinalFactReader(calleeFact, apManager),
            conditionEvaluator,
            JIRTaintCleanActionEvaluator(typeResolver)
        )

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

    override fun propagateZeroToFactResolutionFailure(
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): Set<CallToReturnZFact> = buildSet {
        propagateUnresolvedDemand(
            factAp = currentFactAp,
            startFactBase = startFactBase,
            addSideEffectRequirement = { factReader ->
                check(!factReader.hasRefinement) { "Can't refine Zero fact" }
            },
            addCallToReturn = { factReader, factAp, trace ->
                check(!factReader.hasRefinement) { "Can't refine Zero fact" }
                this += CallToReturnZFact(factAp, trace)
            },
        )
    }

    override fun propagateFactToFactResolutionFailure(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): Set<FactCallFailureFact> = buildSet {
        propagateUnresolvedDemand(
            factAp = currentFactAp,
            startFactBase = startFactBase,
            addSideEffectRequirement = { factReader ->
                this += SideEffectRequirement(factReader.refineFact(initialFactAp.replaceExclusions(ExclusionSet.Empty)))
            },
            addCallToReturn = { factReader, factAp, trace ->
                this += CallToReturnFFact(
                    factReader.refineFact(initialFactAp),
                    factReader.refineFact(factAp),
                    trace
                )
            },
        )
    }

    override fun propagateNDFactToFactResolutionFailure(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): Set<CallToReturnNonDistributiveFact> = buildSet {
        propagateUnresolvedDemand(
            factAp = currentFactAp,
            startFactBase = startFactBase,
            addSideEffectRequirement = { factReader ->
                check(!factReader.hasRefinement) { "Can't refine NDF2F edge" }
            },
            addCallToReturn = { factReader, factAp, trace ->
                check(!factReader.hasRefinement) { "Can't refine NDF2F edge" }
                this += CallToReturnNonDistributiveFact(initialFacts, factAp, trace)
            },
        )
    }

    override fun propagateUnresolvedCallFact(
        factAp: FinalFactAp,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo?) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
    ) {
        error("Backward unresolved call propagation requires the start fact base")
    }

    private fun propagateUnresolvedDemand(
        factAp: FinalFactAp,
        startFactBase: AccessPathBase,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo?) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
    ) {
        if (startFactBase != AccessPathBase.Return) {
            addCallToReturn(FinalFactReader(factAp, apManager), factAp, null)
        }

        val factReader = FinalFactReader(factAp, apManager)
        val passFactReader = FinalFactReader(factAp.rebase(startFactBase), apManager)

        val passEvaluator = TaintPassActionInverseEvaluator(
            apManager, analysisContext.factTypeChecker, passFactReader, typeResolver
        )

        val passRules = taintCtx.passRulesForCallStatement(statement, callExpr, returnValue, passFactReader.factAp)
            .toMutableList()

        analysisContext.analysisManager.params.defaultGetModel?.run {
            passRules += defaultPropagationRules(callExpr.callee)
        }

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
