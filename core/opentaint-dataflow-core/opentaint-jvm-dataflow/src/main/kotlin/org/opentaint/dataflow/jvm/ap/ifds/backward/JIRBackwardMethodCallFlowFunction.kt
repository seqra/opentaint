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
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToStartZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.FactCallFailureFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.SideEffectRequirement
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.ZeroCallFact
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.configuration.TaintCleanReach
import org.opentaint.dataflow.configuration.jvm.PositionAccessor
import org.opentaint.dataflow.configuration.jvm.PositionWithAccess
import org.opentaint.dataflow.configuration.jvm.RemoveMark
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodPositionBaseTypeResolver
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.isApplicable
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallCleaner
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallRuleBasedSummaryRewriter
import org.opentaint.dataflow.jvm.ap.ifds.analysis.aliasesPersistedThroughCall
import org.opentaint.dataflow.jvm.ap.ifds.analysis.apAccessor
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.jvm.ap.ifds.trace.JIRMethodCallPrecondition
import org.opentaint.dataflow.jvm.util.callee
import org.opentaint.dataflow.taint.EvaluatedPass
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.TaintFactAwareConditionEvaluator
import org.opentaint.dataflow.taint.TaintPassActionPreconditionEvaluator
import org.opentaint.ir.api.jvm.JIRType
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRInstanceCallExpr
import org.opentaint.jvm.graph.JMethodEnterInst

class JIRBackwardMethodCallFlowFunction(
    private val apManager: ApManager,
    private val analysisContext: JIRBackwardMethodAnalysisContext,
    private val returnValue: JIRImmediate?,
    private val callExpr: JIRCallExpr,
    private val statement: JIRInst,
) : MethodCallFlowFunction.Default {
    private val rules by lazy { JIRBackwardTaintRules(apManager, analysisContext) }

    private val precondition by lazy {
        JIRMethodCallPrecondition(apManager, analysisContext, returnValue, callExpr, statement)
    }

    private val cleaner by lazy {
        JIRMethodCallCleaner(apManager, analysisContext, returnValue, callExpr, statement)
    }

    private val summaryRewriter by lazy {
        JIRMethodCallRuleBasedSummaryRewriter(statement, analysisContext, apManager)
    }

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
                val sourceMatches = rules.matchCallSources(statement, precondition, callerFact, startFactBase)
                rules.recordSourceMatches(sourceMatches)
                sourceMatches.reader?.let { factReader.updateRefinement(it) }
                conditionDemands += sourceMatches.conditionDemands

                cleaner.applyCleanersOrCallToStart(
                    factReader, callerFact, startFactBase,
                    addCallToReturn, addCallToStart, addUnchecked,
                    ::cleanerInputs
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
        rules.methodEntryMarks(enter) { (it.position as? PositionWithAccess)?.access == PositionAccessor.AnyFieldAccessor }
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

            val passEvaluator = TaintPassActionPreconditionEvaluator(
                passFactReader, analysisContext.factTypeChecker, typeResolver
            )

            val passes = mutableListOf<EvaluatedPass>()
            precondition.evaluatePassRules(passEvaluator, mapExit2Return = { listOf(it) }) { rule, action, fact, _ ->
                passes += EvaluatedPass(rule, action, fact)
            }

            for (pass in passes) {
                cleaner.applyCleaners(passFactReader, pass.fact, ::cleanerInputs, onDrop = { }) { cleaned ->
                    val mappedFact = rules.mapCalleeToCaller(statement, cleaned.factAp) ?: return@applyCleaners
                    addCallToReturn(passFactReader, mappedFact, TraceInfo.Rule(pass.rule, pass.action))
                }
            }

            factReader.updateRefinement(passFactReader)
        }

        if (factReader.hasRefinement) {
            addSideEffectRequirement(factReader)
        }
    }
}
