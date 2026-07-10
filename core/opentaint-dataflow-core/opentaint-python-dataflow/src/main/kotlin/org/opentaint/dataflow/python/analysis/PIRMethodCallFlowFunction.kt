package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnFFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnNonDistributiveFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToStartZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.FactCallFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.ZeroCallFact
import org.opentaint.dataflow.configuration.python.TaintConfigurationItem
import org.opentaint.dataflow.configuration.python.serialized.PIRUserDefinedRuleInfo
import org.opentaint.dataflow.python.PIRCallAnyArgumentResolver
import org.opentaint.dataflow.python.PIRCallAtomEvaluator
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.PIRConditionRewriter
import org.opentaint.dataflow.python.PIRFlowFunctionUtils
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.resolveAp
import org.opentaint.dataflow.python.PIRSimpleFactAwareConditionEvaluator
import org.opentaint.dataflow.python.adapter.callExpr
import org.opentaint.dataflow.python.alias.forEachAliasAfterCallStatement
import org.opentaint.dataflow.taint.DefaultFactWithMarkAfterAnyFieldResolver.Companion.createMarkAfterAccessorResolver
import org.opentaint.dataflow.taint.EvaluatedCleanAction
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.TaintFactAwareConditionEvaluator
import org.opentaint.dataflow.taint.TaintPassActionEvaluator
import org.opentaint.dataflow.taint.applyCleanerActions
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
    private val rulesProvider get() = ctx.taint.taintConfig

    private val callExpr = callInst.callExpr ?: error("Unexpected null call expr")

    private val resolvedMethods by lazy { callResolver.resolveCall(callInst) } // TODO apply rules separately

    private val summaryRewriter by lazy {
        PIRCallRuleBasedSummaryRewriter(callInst, ctx, apManager, resolvedMethods)
    }

    override fun propagateZeroToZero(): Set<ZeroCallFact> {
        val result = mutableSetOf<ZeroCallFact>()

        result.add(CallToReturnZeroFact)

        val conditionRewriter = callConditionRewriter(callInst)
        applySourceRules(emptySet(), null, ExclusionSet.Universe,
            conditionRewriter,
            createFinalFact = { it, trace ->
                result += CallToReturnZFact(factAp = it, trace)
            },
            createEdge = { initial, it, trace ->
                result += CallToReturnFFact(initial, it, trace)
            },
            createNDEdge = { initial, it, trace ->
                result += CallToReturnNonDistributiveFact(initial, it, trace)
            }
        )

        applySinkRules(initialFacts = emptySet(), factReader = null, conditionRewriter) {
            check(it is ZeroCallFact)
            result += it
        }

        result.add(CallToStartZeroFact)

        return result
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

        val conditionRewriter = callConditionRewriter(callInst)
        val reader = FinalFactReader(factAp, apManager)

        applySinkRules(initialFacts, reader, conditionRewriter, addUnchecked)

        applySourceRules(
            initialFacts, reader, exclusion, conditionRewriter,
            createFinalFact = { it, trace ->
                addCallToReturn(reader, it, trace)
            },
            createEdge = { initial, it, trace ->
                addUnchecked(CallToReturnFFact(initial, it, trace))
            },
            createNDEdge = { initial, it, trace ->
                addUnchecked(CallToReturnNonDistributiveFact(initial, it, trace))
            }
        )

        ctx.methodCallFactMapper.mapMethodCallToStartFlowFact(
            callInst,
            callInst.location.method,
            callExpr,
            returnValue,
            factAp,
            FactTypeChecker.Dummy,
        ) { callerFact, startFactBase ->
            applyCleanersOrCallToStart(
                conditionRewriter,
                reader,
                callerFact,
                startFactBase,
                addCallToReturn,
                addCallToStart,
                addUnchecked,
            )
        }

        if (reader.hasRefinement) {
            addSideEffectRequirement(reader)
        }
    }

    private fun applyCleanersOrCallToStart(
        conditionRewriter: PIRConditionRewriter,
        originalFactReader: FinalFactReader,
        unmappedCallerFactAp: FinalFactAp,
        startFactBase: AccessPathBase,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo) -> Unit,
        addCallToStart: (factReader: FinalFactReader, callerFactAp: FinalFactAp, startFactBase: AccessPathBase, TraceInfo) -> Unit,
        addCallToReturnUnchecked: (MethodCallFlowFunction.CallFact) -> Unit,
    ) {
        val callerFact = unmappedCallerFactAp.rebase(startFactBase)
        val conditionFactReader = FinalFactReader(callerFact, apManager)

        val conditionEvaluator = TaintFactAwareConditionEvaluator(
            listOf(conditionFactReader),
            markAfterAnyAccessorResolver = null
        )

        val simpleConditionEvaluator = PIRSimpleFactAwareConditionEvaluator(conditionRewriter, conditionEvaluator)
        val cleaner = PIRTaintCleanActionEvaluator(callInst)

        val factReaderBeforeCleaner = FinalFactReader(callerFact, apManager)
        val cleanerResults = applyCleaner(factReaderBeforeCleaner, simpleConditionEvaluator, cleaner)

        originalFactReader.updateRefinement(conditionFactReader)

        for (cleanerResult in cleanerResults) {
            val factReaderAfterCleaner = cleanerResult.fact
            if (factReaderAfterCleaner == null) {
                val trace = cleanerResult.action
                    ?.takeIf { (it.rule as? TaintConfigurationItem)?.info is PIRUserDefinedRuleInfo }
                    ?.let { TraceInfo.Rule(it.rule, it.action) }
                addCallToReturnUnchecked(MethodCallFlowFunction.Drop(trace))
                continue
            }

            propagateCleanedFact(
                factReaderAfterCleaner,
                originalFactReader,
                startFactBase,
                addCallToStart
            )
        }
    }

    private fun propagateCleanedFact(
        factReaderAfterCleaner: FinalFactReader,
        originalFactReader: FinalFactReader,
        startFactBase: AccessPathBase,
        addCallToStart: (factReader: FinalFactReader, callerFactAp: FinalFactAp, startFactBase: AccessPathBase, TraceInfo) -> Unit,
    ) {
        originalFactReader.updateRefinement(factReaderAfterCleaner)

        val cleanedFact = factReaderAfterCleaner.factAp
        check(cleanedFact.base == startFactBase)

        val unmappedFact = cleanedFact.rebase(originalFactReader.factAp.base)

        addCallToStart(originalFactReader, unmappedFact, startFactBase, TraceInfo.Flow)
    }

    private fun applyCleaner(
        initialFact: FinalFactReader,
        conditionEvaluator: PIRSimpleFactAwareConditionEvaluator,
        cleanEvaluator: PIRTaintCleanActionEvaluator,
    ): List<EvaluatedCleanAction> {
        val rules = resolvedMethods
            .flatMap { rulesProvider.cleanersForMethod(it) }
            .filter { conditionEvaluator.eval(it.condition) }

        return rules.applyCleanerActions(
            evalAction = { fact, rule, action -> cleanEvaluator.evaluate(fact, rule, action) },
            itemRule = { it },
            itemActions = { it.cleans },
            initial = EvaluatedCleanAction.initial(initialFact),
        )
    }

    override fun propagateUnresolvedCallFact(
        factAp: FinalFactAp,
        startFactBase: AccessPathBase,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo?) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit
    ) {
        val factReader = FinalFactReader(factAp, apManager)

        unresolvedCallPropagateDefault(factReader, factAp, addCallToReturn)

        applyPassRules(factAp, factReader, factAp.rebase(startFactBase), startFactBase, addCallToReturn)

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
        initialFacts: Set<InitialFactAp>,
        factReader: FinalFactReader?,
        exclusionSet: ExclusionSet,
        conditionRewriter: PIRConditionRewriter,
        createFinalFact: (FinalFactAp, TraceInfo) -> Unit,
        createEdge: (InitialFactAp, FinalFactAp, TraceInfo) -> Unit,
        createNDEdge: (Set<InitialFactAp>, FinalFactAp, TraceInfo) -> Unit,
    ) {
        val sourceRules = resolvedMethods.flatMapTo(mutableListOf()) { method ->
            rulesProvider.sourcesForMethod(method)
        }

        val taintUtil = PIRMethodCallTaintUtil(callExpr, ctx, callInst, apManager)

        taintUtil.applySourceRules(
            sourceRules = sourceRules,
            initialFacts = initialFacts,
            conditionRewriter = conditionRewriter,
            factReader = factReader,
            exclusion = exclusionSet,
            createFinalFact = { srcF, trace ->
                srcF.forEachSourceFactWithAliases {
                    createFinalFact(it, trace)
                }
            },
            createEdge = { initial, srcF, trace ->
                srcF.forEachSourceFactWithAliases {
                    createEdge(initial, it, trace)
                }
            },
            createNDEdge = { initial, srcF, trace ->
                srcF.forEachSourceFactWithAliases {
                    createNDEdge(initial, it, trace)
                }
            },
        )
    }

    private fun applySinkRules(
        initialFacts: Set<InitialFactAp>,
        factReader: FinalFactReader?,
        conditionRewriter: PIRConditionRewriter,
        addUnchecked: (MethodCallFlowFunction.CallFact) -> Unit
    ) {
        val sinkRules = resolvedMethods.flatMapTo(mutableListOf()) { method ->
            rulesProvider.sinksForMethod(method)
        }

        val taintUtil = PIRMethodCallTaintUtil(callExpr, ctx, callInst, apManager)

        val markAfterAnyAccessorResolver = createMarkAfterAccessorResolver(
            ctx.methodEntryPoint, initialFacts
        ) { i, k ->
            addUnchecked(MethodCallFlowFunction.FactSideEffect(i, k))
        }

        taintUtil.applySinkRules(sinkRules, conditionRewriter, factReader, markAfterAnyAccessorResolver)
    }

    private fun applyPassRules(
        originalFact: FinalFactAp,
        originalFactReader: FinalFactReader,
        mappedFact: FinalFactAp,
        startFactBase: AccessPathBase,
        propagateFact: (FinalFactReader, FinalFactAp, TraceInfo) -> Unit,
    ) {
        val typeChecker = FactTypeChecker.Dummy
        var passRules = resolvedMethods.flatMapTo(mutableListOf()) { method ->
            rulesProvider.passThroughForMethod(method)
        }

        if (passRules.isEmpty()) {
            passRules = resolvedMethods.flatMapTo(mutableListOf()) { method ->
                rulesProvider.passThroughForMethod(method, bySimpleName = true)
            }
        }

        val reader = FinalFactReader(mappedFact, apManager)
        val evaluator = TaintPassActionEvaluator(
            apManager, typeChecker, reader,
            PIRFlowFunctionUtils.DummyPositionTypeResolver
        )

        val conditionRewriter = callConditionRewriter(callInst)
        val simpleConditionEvaluator = PIRSimpleFactAwareConditionEvaluator(conditionRewriter, null)

        val passThroughFacts = passRules.maybeFlatMap { rule ->
            if (!simpleConditionEvaluator.eval(rule.condition)) return@maybeFlatMap Maybe.none()

            rule.copy.maybeFlatMap { action ->
                val from = action.from.resolveAp(callInst) ?: return@maybeFlatMap Maybe.none()
                val to = action.to.resolveAp(callInst) ?: return@maybeFlatMap Maybe.none()

                evaluator.propagateData(rule, action, from, to)
            }
        }

        if (startFactBase !is AccessPathBase.ClassStatic) {
            ctx.taint.externalMethodTracker?.trackExternalMethod(
                method = callInst.resolvedCallee ?: callInst.callee.toString(),
                signature = "args:${callInst.args.size}",
                factPosition = startFactBase.toString(),
                rulesApplied = passThroughFacts.isSome,
            )
        }

        passThroughFacts.onSome { facts ->
            facts.forEach { evp ->
                val traceInfo = TraceInfo.Rule(evp.rule, evp.action)
                val rewrittenFacts = summaryRewriter.rewriteSummaryFact(evp.fact)
                for ((unrefinedFact, factRefinement) in rewrittenFacts) {
                    val fact = factRefinement.refineFact(unrefinedFact)
                    reader.updateRefinement(factRefinement)

                    ctx.methodCallFactMapper.mapMethodExitToReturnFlowFact(callInst, fact, typeChecker).forEach { mappedFact ->
                        mappedFact.forEachFactWithAliases(originalFact) { propagateFact(reader, it, traceInfo) }
                    }
                }
            }
        }

        originalFactReader.updateRefinement(reader)
    }

    private inline fun FinalFactAp.forEachSourceFactWithAliases(crossinline body: (FinalFactAp) -> Unit) =
        forEachFactWithAliases(originalFact = null, body)

    private inline fun FinalFactAp.forEachFactWithAliases(originalFact: FinalFactAp?,  crossinline body: (FinalFactAp) -> Unit) {
        body(this)

        if (originalFact != null && originalFact == this) {
            return
        }

        ctx.aliasAnalysis?.forEachAliasAfterCallStatement(callInst, this) { aliased ->
            body(aliased)
        }
    }

    private fun callConditionRewriter(call: PIRCall) = PIRConditionRewriter(
        PIRCallAnyArgumentResolver(call), PIRCallAtomEvaluator(call), call
    )
}
