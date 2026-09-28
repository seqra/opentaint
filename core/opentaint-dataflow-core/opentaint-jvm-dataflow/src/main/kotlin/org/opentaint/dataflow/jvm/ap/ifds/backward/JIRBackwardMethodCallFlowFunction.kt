package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnFFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnNonDistributiveFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.FactCallFailureFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.SideEffectRequirement
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.TaintCleanReach
import org.opentaint.dataflow.configuration.jvm.PositionAccessor
import org.opentaint.dataflow.configuration.jvm.PositionWithAccess
import org.opentaint.dataflow.configuration.jvm.RemoveMark
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.accept
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.applicableRules
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallFlowFunction
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallRuleBasedSummaryRewriter
import org.opentaint.dataflow.jvm.ap.ifds.analysis.aliasesPersistedThroughCall
import org.opentaint.dataflow.jvm.ap.ifds.analysis.apAccessor
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardTaintRulesProvider.Companion.markPositions
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.jvm.util.callee
import org.opentaint.dataflow.taint.EvaluatedPass
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.PassActionEvaluator
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.TaintFactAwareConditionEvaluator
import org.opentaint.dataflow.taint.TaintPassActionEvaluator
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
) : JIRMethodCallFlowFunction(apManager, analysisContext, returnValue, callExpr, statement, generateTrace = false) {
    private val summaryRewriter by lazy {
        JIRMethodCallRuleBasedSummaryRewriter(statement, analysisContext, apManager)
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

        for (demand in demands) {
            val demandReader = if (demand === factAp) factReader else FinalFactReader(demand, apManager)
            applyTaintRules(initialFacts, exclusion, demandReader, { reader, fact, trace ->
                factReader.updateRefinement(reader)
                addCallToReturn(factReader, fact, trace)
            }, addUnchecked)
            factReader.updateRefinement(demandReader)

            JIRBackwardMethodCallFactMapper.mapMethodCallToStartFlowFact(
                statement, callExpr.callee, callExpr, returnValue, demand, analysisContext.factTypeChecker
            ) { callerFact, startFactBase ->
                applyCleaners(factReader, callerFact, startFactBase, addCallToReturn, addUnchecked) { reader, fact, base, trace ->
                    for ((rewritten, rewriteReader) in summaryRewriter.rewriteSummaryFact(fact.rebase(base))) {
                        reader.updateRefinement(rewriteReader)
                        addCallToStart(reader, rewritten.rebase(fact.base), base, trace)
                    }
                }
            }
        }

        if (factReader.hasRefinement) {
            addSideEffectRequirement(factReader)
        }
    }

    private fun applyCleaners(
        factReader: FinalFactReader,
        callerFact: FinalFactAp,
        startFactBase: AccessPathBase,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo) -> Unit,
        addUnchecked: (MethodCallFlowFunction.CallFact) -> Unit,
        addCallToStart: (FinalFactReader, FinalFactAp, AccessPathBase, TraceInfo) -> Unit,
    ) {
        for (input in cleanerInputs(callerFact.rebase(startFactBase))) {
            applyCleanersOrCallToStart(
                factReader, input, startFactBase,
                { reader, fact, trace -> addCallToReturn(reader, fact.rebase(callerFact.base), trace) },
                { reader, fact, base, trace -> addCallToStart(reader, fact.rebase(callerFact.base), base, trace) },
                addUnchecked
            )
        }
    }

    private fun callSiteAliasDemands(factReader: FinalFactReader): List<FinalFactAp> {
        val aliasAnalysis = analysisContext.aliasAnalysis ?: return emptyList()
        val factAp = factReader.factAp

        val result = mutableListOf<FinalFactAp>()
        for (local in callLocals) {
            for (alias in aliasAnalysis.aliasesPersistedThroughCall(local, statement)) {
                if (alias.base != factAp.base) continue
                if (alias.accessors.isEmpty() && local == factAp.base) continue

                val position = alias.accessors.fold(PositionAccess.Simple(factAp.base) as PositionAccess) { position, accessor ->
                    PositionAccess.Complex(position, accessor.apAccessor())
                }
                if (!factReader.containsPosition(position)) continue

                val unaliased = alias.accessors.fold(factAp.rebase(local) as FinalFactAp?) { fact, accessor ->
                    fact?.readAccessor(accessor.apAccessor())
                }
                unaliased?.let { result += it }
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

    private fun cleanerInputs(calleeFact: FinalFactAp): List<FinalFactAp> {
        val marks = starRootMarksRemoved(calleeFact)
        if (marks.isEmpty() || marks.any { it in methodEntryAnyFieldMarks }) return listOf(calleeFact)
        return analysisContext.starUnroller.unroll(calleeFact, calleeBaseType(calleeFact.base)) ?: listOf(calleeFact)
    }

    private fun starRootMarksRemoved(calleeFact: FinalFactAp): Set<TaintMarkAccessor> {
        if (!calleeFact.startsWithAccessor(AnyAccessor)) return emptySet()
        val star = calleeFact.readAccessor(AnyAccessor) ?: return emptySet()
        val root = PositionAccess.Simple(calleeFact.base)

        val cleanRules = analysisContext.taint.cleanRulesForCallStatement(statement, callExpr, returnValue, calleeFact)
        val conditionEvaluator = TaintFactAwareConditionEvaluator(
            listOf(FinalFactReader(calleeFact, apManager)), markAfterAnyAccessorResolver = null
        )

        return cleanRules.applicableRules(conditionEvaluator).flatMapTo(hashSetOf()) { rule ->
            rule.actionsAfter.mapNotNull { action ->
                if (action !is RemoveMark || action.reach != TaintCleanReach.Exact) return@mapNotNull null
                if (action.position.resolveAp() != root) return@mapNotNull null
                TaintMarkAccessor(action.mark.name).takeIf { star.startsWithAccessor(it) }
            }
        }
    }

    private val methodEntryAnyFieldMarks: Set<TaintMarkAccessor> by lazy {
        val enter = analysisContext.forwardEntryPoint as? JMethodEnterInst ?: return@lazy emptySet()
        analysisContext.taint.sinkRulesForMethodEntry(enter, fact = null).flatMapTo(hashSetOf()) { rule ->
            rule.rule.condition.markPositions()
                .filter { (it.position as? PositionWithAccess)?.access == PositionAccessor.AnyFieldAccessor }
                .map { TaintMarkAccessor(it.mark.name) }
        }
    }

    private fun calleeBaseType(base: AccessPathBase): JIRType? = when (base) {
        is AccessPathBase.Return -> returnValue?.type
        is AccessPathBase.This -> (callExpr as? JIRInstanceCallExpr)?.instance?.type
        is AccessPathBase.Argument -> callExpr.args.getOrNull(base.idx)?.type
        else -> null
    }

    override fun propagateZeroToFactResolutionFailure(currentFactAp: FinalFactAp, startFactBase: AccessPathBase) =
        buildSet<CallToReturnZFact> {
            propagateUnresolvedCallFact(
                currentFactAp, startFactBase,
                addSideEffectRequirement = { check(!it.hasRefinement) { "Can't refine Zero fact" } },
                addCallToReturn = { factReader, factAp, trace ->
                    check(!factReader.hasRefinement) { "Can't refine Zero fact" }
                    this += CallToReturnZFact(factAp, trace)
                },
            )
        }

    override fun propagateFactToFactResolutionFailure(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase,
    ) = buildSet<FactCallFailureFact> {
        propagateUnresolvedCallFact(
            currentFactAp, startFactBase,
            addSideEffectRequirement = { factReader ->
                this += SideEffectRequirement(factReader.refineFact(initialFactAp.replaceExclusions(ExclusionSet.Empty)))
            },
            addCallToReturn = { factReader, factAp, trace ->
                this += CallToReturnFFact(factReader.refineFact(initialFactAp), factReader.refineFact(factAp), trace)
            },
        )
    }

    override fun propagateNDFactToFactResolutionFailure(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase,
    ) = buildSet<CallToReturnNonDistributiveFact> {
        propagateUnresolvedCallFact(
            currentFactAp, startFactBase,
            addSideEffectRequirement = { check(!it.hasRefinement) { "Can't refine NDF2F edge" } },
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
    ): Unit = error("Unresolved backward call requires the start fact base")

    private fun propagateUnresolvedCallFact(
        factAp: FinalFactAp,
        startFactBase: AccessPathBase,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo?) -> Unit,
    ) {
        if (startFactBase != AccessPathBase.Return) {
            for ((keptFact, keptReader) in summaryRewriter.rewriteSummaryFact(factAp)) {
                addCallToReturn(keptReader, keptReader.refineFact(keptFact), null)
            }
        }

        val factReader = FinalFactReader(factAp, apManager)

        for ((demand, rewriteReader) in summaryRewriter.rewriteSummaryFact(factAp.rebase(startFactBase))) {
            val passFactReader = FinalFactReader(rewriteReader.refineFact(demand), apManager)
            passFactReader.updateRefinement(rewriteReader)

            for (pass in invertedPassThrough(passFactReader)) {
                val trace = TraceInfo.Rule(pass.rule, pass.action)
                applyCleaners(passFactReader, pass.fact, pass.fact.base, { _, _, _ -> }, {}) { reader, fact, _, _ ->
                    JIRBackwardMethodCallFactMapper
                        .mapMethodExitToReturnFlowFact(statement, fact, analysisContext.factTypeChecker)
                        .singleOrNull()
                        ?.let { addCallToReturn(reader, it, trace) }
                }
            }

            factReader.updateRefinement(passFactReader)
        }

        if (factReader.hasRefinement) {
            addSideEffectRequirement(factReader)
        }
    }

    private fun invertedPassThrough(factReader: FinalFactReader): List<EvaluatedPass> {
        val evaluator = TaintPassActionEvaluator(apManager, analysisContext.factTypeChecker, factReader, typeResolver)
        val inverse = object : PassActionEvaluator<EvaluatedPass> {
            override fun propagateData(
                rule: CommonTaintConfigurationItem, action: CommonTaintAction, from: PositionAccess, to: PositionAccess,
            ) = evaluator.propagateData(rule, action, to, from)

            override fun propagateTaint(
                rule: CommonTaintConfigurationItem, action: CommonTaintAction,
                from: PositionAccess, to: PositionAccess, mark: TaintMarkAccessor,
            ) = evaluator.propagateTaint(rule, action, to, from, mark)
        }

        val passRules = analysisContext.taint.passRulesForCallStatement(statement, callExpr, returnValue, fact = null).toMutableList()
        analysisContext.analysisManager.params.defaultGetModel?.run {
            passRules += defaultPropagationRules(callExpr.method.method)
        }

        val passes = mutableListOf<EvaluatedPass>()
        for (rule in passRules) {
            if (rule.condition.isFalse) continue
            rule.rule.actionsAfter.forEach { action -> inverse.accept(rule.rule, action).onSome { passes += it } }
        }
        return passes.filter { it.fact != factReader.factAp }
    }
}
