package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnFFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToStartFFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToStartZFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToStartZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.FactCallFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.FactCallFailureFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.NDFactCallFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.NDFactCallFailureFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.SideEffectRequirement
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.Unchanged
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.ZeroCallFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.ZeroCallFailureFact
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.PIRConditionRewriter
import org.opentaint.dataflow.python.PIRFlowFunctionUtils
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.resolveAp
import org.opentaint.dataflow.python.adapter.callExpr
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.PositionTypeResolver
import org.opentaint.dataflow.taint.TaintPassActionEvaluator
import org.opentaint.ir.api.common.CommonType
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.util.onSome
import kotlin.collections.plusAssign

class PIRMethodCallFlowFunction(
    private val callInst: PIRCall,
    private val method: PIRFunction,
    private val ctx: PIRMethodAnalysisContext,
    private val apManager: ApManager,
    private val returnValue: CommonValue?,
    private val callResolver: PIRCallResolver,
) : MethodCallFlowFunction {
    private val callExpr = callInst.callExpr ?: error("Unexpected null call expr")

    private val resolvedMethods by lazy { callResolver.resolveCall(callInst) } // TODO apply rules separately

    override fun propagateZeroToZero(): Set<ZeroCallFact> {
        val results = mutableSetOf<ZeroCallFact>()

        results.add(CallToReturnZeroFact)

        applySourceRules(ExclusionSet.Universe) { fact, traceInfo ->
            results += CallToReturnZFact(fact, traceInfo)
        }

        results.add(CallToStartZeroFact)

        return results
    }

    override fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<ZeroCallFact> = buildSet {
        propagateFact(
            currentFactAp = currentFactAp,
            skipCall = { this += Unchanged },
            addCallToStart = { factReader, callerFactAp, startFactBase ->
                check(!factReader.hasRefinement) { "Can't refine Zero fact" }
                this += CallToStartZFact(callerFactAp, startFactBase, null)
            },
            addCallToReturn = { factReader, factAp ->
                check(!factReader.hasRefinement) { "Can't refine Zero fact" }
                this += CallToReturnZFact(factAp, null)
            },
            addSideEffectRequirement = { factReader ->
                check(!factReader.hasRefinement) { "Can't refine Zero fact" }
            },
        )
    }

    override fun propagateFactToFact(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
    ): Set<FactCallFact> = buildSet {
        propagateFact(
            currentFactAp = currentFactAp,
            skipCall = { this += Unchanged },
            addSideEffectRequirement = { factReader ->
                this += SideEffectRequirement(factReader.refineFact(initialFactAp.replaceExclusions(ExclusionSet.Empty)))
            },
            addCallToReturn = { factReader, factAp ->
                this += CallToReturnFFact(
                    factReader.refineFact(initialFactAp),
                    factReader.refineFact(factAp),
                    traceInfo = null
                )
            },
            addCallToStart = { factReader, callerFactAp, startFactBase ->
                this += CallToStartFFact(
                    factReader.refineFact(initialFactAp),
                    factReader.refineFact(callerFactAp),
                    startFactBase,
                    traceInfo = null,
                )
            },
        )
    }

    override fun propagateNDFactToFact(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
    ): Set<NDFactCallFact> = setOf(Unchanged)

    // --- Shared propagation logic ---

    /**
     * Shared logic for both zero-to-fact and fact-to-fact propagation at call sites.
     * Handles sinks, pass-through rules, and call-to-start mapping.
     *
     * [T] is the specific CallFact subtype ([ZeroCallFact] or [FactCallFact]).
     * [mkCallToReturnFact] creates a call-to-return fact from a rebased fact.
     * [mkCallToStartFact] creates a call-to-start fact from (callerFact, startBase).
     * [mkUnchanged] creates the "unchanged" fact to keep in caller frame.
     */
    private fun propagateFact(
        currentFactAp: FinalFactAp,
        skipCall: () -> Unit,
        addCallToStart: (FinalFactReader, FinalFactAp, AccessPathBase) -> Unit,
        addCallToReturn: (FinalFactReader, FinalFactAp) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
    ) {
        if (!ctx.methodCallFactMapper.factIsRelevantToMethodCall(callInst, returnValue = null, callExpr, currentFactAp)) {
            skipCall()
            return
        }

        val reader = FinalFactReader(currentFactAp, apManager)
        applySinkRules(reader)

        ctx.methodCallFactMapper.mapMethodCallToStartFlowFact(
            callInst,
            callInst.location.method,
            callExpr,
            returnValue,
            currentFactAp,
            FactTypeChecker.Dummy,
        ) { fact, startBase ->
            applyPassRules(reader, fact.rebase(startBase), addCallToReturn)

            addCallToStart(reader, fact, startBase)
        }

        if (reader.hasRefinement) {
            addSideEffectRequirement(reader)
        }
    }

    override fun propagateZeroToZeroResolutionFailure(): Set<ZeroCallFailureFact> =
        setOf(CallToReturnZeroFact)

    override fun propagateZeroToFactResolutionFailure(
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): Set<ZeroCallFailureFact> {
        return setOf(CallToReturnZFact(currentFactAp, traceInfo = null))
    }

    override fun propagateFactToFactResolutionFailure(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): Set<FactCallFailureFact> {
        return setOf(CallToReturnFFact(initialFactAp, currentFactAp, traceInfo = null))
    }

    override fun propagateNDFactToFactResolutionFailure(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): Set<NDFactCallFailureFact> {
        return setOf(
            MethodCallFlowFunction.CallToReturnNonDistributiveFact(initialFacts, currentFactAp, traceInfo = null)
        )
    }

    private fun applySourceRules(
        exclusionSet: ExclusionSet,
        createFinalFact: (FinalFactAp, MethodCallFlowFunction.TraceInfo) -> Unit,
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
        propagateFact: (FinalFactReader, FinalFactAp) -> Unit,
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

        passRules.forEach { rule ->
            rule.copy.forEach { action ->
                val from = action.from.resolveAp() ?: return@forEach
                val to = action.to.resolveAp() ?: return@forEach

                evaluator.propagateData(rule, action, from, to).onSome { facts ->
                    facts.forEach { fact ->
                        ctx.methodCallFactMapper.mapMethodExitToReturnFlowFact(callInst, fact.fact, typeChecker).forEach { mappedFact ->
                            propagateFact(reader, mappedFact)
                        }
                    }
                }
            }
        }

        originalFactReader.updateRefinement(reader)
    }
}
