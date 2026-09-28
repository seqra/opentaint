package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
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
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.accept
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallFlowFunction
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallRuleBasedSummaryRewriter
import org.opentaint.dataflow.jvm.ap.ifds.analysis.aliasesPersistedThroughCall
import org.opentaint.dataflow.jvm.ap.ifds.analysis.apAccessor
import org.opentaint.dataflow.jvm.util.callee
import org.opentaint.dataflow.taint.EvaluatedPass
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.PassActionEvaluator
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.TaintPassActionEvaluator
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRInstanceCallExpr
import org.opentaint.util.onSome

internal class JIRBackwardMethodCallFlowFunction(
    private val apManager: ApManager,
    private val analysisContext: JIRMethodAnalysisContext,
    private val returnValue: JIRImmediate?,
    private val callExpr: JIRCallExpr,
    private val statement: JIRInst,
) : MethodCallFlowFunction.Default {
    private val forward = JIRMethodCallFlowFunction(apManager, analysisContext, returnValue, callExpr, statement, generateTrace = false)

    private val summaryRewriter by lazy {
        JIRMethodCallRuleBasedSummaryRewriter(statement, analysisContext, apManager)
    }

    private val cleanActionEvaluator = JIRBackwardTaintCleanActionEvaluator()

    override fun propagateZeroToZero(): Set<MethodCallFlowFunction.ZeroCallFact> = forward.propagateZeroToZero()

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
            forward.applyTaintRules(initialFacts, exclusion, demandReader, { reader, fact, trace ->
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
        forward.applyCleanersOrCallToStart(
            factReader, callerFact, startFactBase,
            { reader, fact, trace -> addCallToReturn(reader, fact.rebase(callerFact.base), trace) },
            { reader, fact, base, trace -> addCallToStart(reader, fact.rebase(callerFact.base), base, trace) },
            addUnchecked,
            cleanActionEvaluator.evaluator(forward.typeResolver),
        )
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
        val evaluator = TaintPassActionEvaluator(apManager, analysisContext.factTypeChecker, factReader, forward.typeResolver)
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
