package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToStartZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.FactCallFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.ZeroCallFact
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.PIRConditionRewriter
import org.opentaint.dataflow.python.PIRFlowFunctionUtils
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.resolveAp
import org.opentaint.dataflow.python.adapter.callExpr
import org.opentaint.dataflow.python.alias.forEachAliasAfterCallStatement
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.TaintPassActionEvaluator
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.util.Maybe
import org.opentaint.util.maybeFlatMap
import org.opentaint.util.onSome
import kotlin.collections.plusAssign

class PIRMethodCallFlowFunction(
    private val callInst: PIRCall,
    private val method: PIRFunction,
    private val ctx: PIRMethodAnalysisContext,
    private val apManager: ApManager,
    private val returnValue: CommonValue?,
    private val callResolver: PIRCallResolver,
) : MethodCallFlowFunction.Default {
    private val callExpr = callInst.callExpr ?: error("Unexpected null call expr")

    private val resolvedMethods by lazy { callResolver.resolveCall(callInst) } // TODO apply rules separately

    private val summaryRewriter by lazy {
        PIRCallRuleBasedSummaryRewriter(callInst, ctx, apManager, resolvedMethods)
    }

    override fun propagateZeroToZero(): Set<ZeroCallFact> {
        val results = mutableSetOf<ZeroCallFact>()

        results.add(CallToReturnZeroFact)

        applySourceRules(ExclusionSet.Universe) { fact, traceInfo ->
            results += CallToReturnZFact(fact, traceInfo)
        }

        results.add(CallToStartZeroFact)

        return results
    }


    /**
     * Shared logic for both zero-to-fact and fact-to-fact propagation at call sites.
     * Handles sinks, pass-through rules, and call-to-start mapping.
     *
     * [T] is the specific CallFact subtype ([ZeroCallFact] or [FactCallFact]).
     * [mkCallToReturnFact] creates a call-to-return fact from a rebased fact.
     * [mkCallToStartFact] creates a call-to-start fact from (callerFact, startBase).
     * [mkUnchanged] creates the "unchanged" fact to keep in caller frame.
     */
    override fun propagateFact(
        initialFacts: Set<InitialFactAp>,
        exclusion: ExclusionSet,
        factAp: FinalFactAp,
        skipCall: () -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo) -> Unit,
        addCallToStart: (factReader: FinalFactReader, callerFact: FinalFactAp, startFactBase: AccessPathBase, TraceInfo) -> Unit,
        addUnchecked: (MethodCallFlowFunction.CallFact) -> Unit
    ) {
        if (!ctx.methodCallFactMapper.factIsRelevantToMethodCall(callInst, returnValue = null, callExpr, factAp)) {
            skipCall()
            return
        }

        val reader = FinalFactReader(factAp, apManager)
        applySinkRules(reader)

        ctx.methodCallFactMapper.mapMethodCallToStartFlowFact(
            callInst,
            callInst.location.method,
            callExpr,
            returnValue,
            factAp,
            FactTypeChecker.Dummy,
        ) { fact, startBase ->
            addCallToStart(reader, fact, startBase, TraceInfo.Flow)
        }

        if (reader.hasRefinement) {
            addSideEffectRequirement(reader)
        }
    }

    override fun propagateUnresolvedCallFact(
        factAp: FinalFactAp,
        startFactBase: AccessPathBase,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo?) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit
    ) {
        val factReader = FinalFactReader(factAp, apManager)

        unresolvedCallPropagateDefault(factReader, factAp, addCallToReturn)

        applyPassRules(factReader, factAp.rebase(startFactBase), addCallToReturn)

        if (factReader.hasRefinement) {
            addSideEffectRequirement(factReader)
        }
    }

    fun unresolvedCallPropagateDefault(
        originalFactReader: FinalFactReader,
        factAp: FinalFactAp,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo?) -> Unit,
    ) {
        summaryRewriter.rewriteSummaryFact(factAp).forEach { (fact, reader) ->
            originalFactReader.updateRefinement(reader)

            addCallToReturn(reader, fact, null)
        }
    }

    private fun applySourceRules(
        exclusionSet: ExclusionSet,
        createFinalFact: (FinalFactAp, TraceInfo) -> Unit,
    ) {
        val sourceRules = resolvedMethods.flatMapTo(mutableListOf()) { method ->
            ctx.taintRules.sourcesForMethod(method)
        }

        val taintUtil = PIRMethodCallTaintUtil(ctx, callInst, callExpr, apManager)
        val conditionRewriter = PIRConditionRewriter

        taintUtil.applySourceRules(
            sourceRules = sourceRules,
            initialFacts = emptySet(),
            conditionRewriter = conditionRewriter,
            factReader = null,
            exclusion = exclusionSet,
            createFinalFact = createFinalFact,
            createEdge = { _, _, _ -> error("Unexpected") },
            createNDEdge = { _, _, _ -> error("Unexpected") },
        )
    }

    private fun applySinkRules(
        factReader: FinalFactReader,
    ) {
        val sinkRules = resolvedMethods.flatMapTo(mutableListOf()) { method ->
            ctx.taintRules.sinksForMethod(method)
        }

        val taintUtil = PIRMethodCallTaintUtil(ctx, callInst, callExpr, apManager)
        val conditionRewriter = PIRConditionRewriter

        taintUtil.applySinkRules(sinkRules, conditionRewriter, factReader, markAfterAnyFieldResolver = null)
    }

    private fun applyPassRules(
        originalFactReader: FinalFactReader,
        mappedFact: FinalFactAp,
        propagateFact: (FinalFactReader, FinalFactAp, TraceInfo) -> Unit,
    ) {
        val typeChecker = FactTypeChecker.Dummy
        val passRules = resolvedMethods.flatMapTo(mutableListOf()) { method ->
            ctx.taintRules.passThroughForMethod(method)
        }

        val reader = FinalFactReader(mappedFact, apManager)
        val evaluator = TaintPassActionEvaluator(
            apManager, typeChecker, reader,
            PIRFlowFunctionUtils.DummyPositionTypeResolver
        )

        val passThroughFacts = passRules.maybeFlatMap { rule ->
            rule.copy.maybeFlatMap { action ->
                val from = action.from.resolveAp() ?: return@maybeFlatMap Maybe.none()
                val to = action.to.resolveAp() ?: return@maybeFlatMap Maybe.none()

                evaluator.propagateData(rule, action, from, to)
            }
        }

        passThroughFacts.onSome { facts ->
            facts.forEach { evp ->
                val traceInfo = TraceInfo.Rule(evp.rule, evp.action)
                val rewrittenFacts = summaryRewriter.rewriteSummaryFact(evp.fact)
                for ((unrefinedFact, factRefinement) in rewrittenFacts) {
                    val fact = factRefinement.refineFact(unrefinedFact)
                    reader.updateRefinement(factRefinement)

                    ctx.methodCallFactMapper.mapMethodExitToReturnFlowFact(callInst, fact, typeChecker).forEach { mappedFact ->
                        propagateFact(reader, mappedFact, traceInfo)

                        ctx.aliasAnalysis?.forEachAliasAfterCallStatement(callInst, mappedFact) {
                            propagateFact(reader, it, traceInfo)
                        }
                    }
                }
            }
        }

        originalFactReader.updateRefinement(reader)
    }
}
