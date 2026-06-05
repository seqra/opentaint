package org.opentaint.dataflow.go.analysis

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
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.ZeroCallFact
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.GoMethodCallFactMapper.factIsRelevantToMethodCall
import org.opentaint.dataflow.go.GoMethodCallFactMapper.mapMethodCallToStartFlowAnyFact
import org.opentaint.dataflow.go.GoMethodCallFactMapper.mapMethodExitToReturnFlowFact
import org.opentaint.dataflow.go.rules.GoRuleConditionRewriter
import org.opentaint.dataflow.go.rules.accept
import org.opentaint.dataflow.go.signature
import org.opentaint.dataflow.taint.DefaultFactWithMarkAfterAnyFieldResolver.Companion.createMarkAfterAccessorResolver
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.PositionTypeResolver
import org.opentaint.dataflow.taint.TaintPassActionEvaluator
import org.opentaint.ir.api.common.CommonType
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRValue
import org.opentaint.util.maybeFlatMap
import org.opentaint.util.onSome

class GoMethodCallFlowFunction(
    private val apManager: ApManager,
    private val context: GoMethodAnalysisContext,
    private val callExpr: GoCallExpr,
    private val statement: GoIRInst,
    private val generateTrace: Boolean,
) : MethodCallFlowFunction.Default {
    private val rulesProvider get() = context.taint.taintConfig

    private val returnValue: GoIRValue?
        get() = GoFlowFunctionUtils.extractResultRegister(statement)

    private val callSignature: GoFunctionSignature?
        get() = callExpr.signature()

    private val summaryRewriter by lazy {
        GoCallRuleBasedSummaryRewriter(statement, callExpr, returnValue, context, apManager)
    }

    override fun propagateZeroToZero(): Set<ZeroCallFact> {
        val result = mutableSetOf(
            CallToReturnZeroFact,
            CallToStartZeroFact,
        )

        applySinkRules(
            emptySet(), null,
            addUnchecked = {
                check(it is ZeroCallFact)
                result.add(it)
            }
        )

        applySourceRules(
            emptySet(), null, ExclusionSet.Universe,
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
        return result
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
        if (!factIsRelevantToMethodCall(statement, returnValue as? CommonValue, callExpr, factAp)) {
            skipCall()
            return
        }

        val factReader = FinalFactReader(factAp, apManager)

        applySinkRules(initialFacts, factReader, addUnchecked)

        applySourceRules(
            initialFacts, factReader, exclusion,
            createFinalFact = { it, trace ->
                addCallToReturn(factReader, it, trace)
            },
            createEdge = { initial, it, trace ->
                addUnchecked(CallToReturnFFact(initial, it, trace))
            },
            createNDEdge = { initial, it, trace ->
                addUnchecked(CallToReturnNonDistributiveFact(initial, it, trace))
            }
        )

        factAp.mapCall2Start { fact, startBase ->
            addCallToStart(factReader, fact, startBase, TraceInfo.Flow)
        }

        if (factReader.hasRefinement) {
            addSideEffectRequirement(factReader)
        }
    }

    private fun applySourceRules(
        initialFacts: Set<InitialFactAp>,
        factReader: FinalFactReader?,
        exclusion: ExclusionSet,
        createFinalFact: (FinalFactAp, TraceInfo) -> Unit,
        createEdge: (InitialFactAp, FinalFactAp, TraceInfo) -> Unit,
        createNDEdge: (Set<InitialFactAp>, FinalFactAp, TraceInfo) -> Unit,
    ) {
        val signature = callSignature ?: return
        val sourceRules = rulesProvider.sourceRulesForCall(signature)
        if (sourceRules.isEmpty()) return

        val taintUtils = GoMethodCallTaintUtil(statement, callExpr, returnValue, context, apManager)
        taintUtils.applySourceRules(
            sourceRules, initialFacts,
            conditionRewriter = GoRuleConditionRewriter(callExpr, statement, returnValue),
            factReader, exclusion,
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
        addUnchecked: (MethodCallFlowFunction.CallFact) -> Unit,
    ) {
        val signature = callSignature ?: return
        val sinkRules = rulesProvider.sinkRulesForCall(signature)
        if (sinkRules.isEmpty()) return

        val markAfterAnyAccessorResolver = createMarkAfterAccessorResolver(
            context.methodEntryPoint, initialFacts
        ) { i, k ->
            addUnchecked(MethodCallFlowFunction.FactSideEffect(i, k))
        }

        val taintUtils = GoMethodCallTaintUtil(statement, callExpr, returnValue, context, apManager)
        taintUtils.applySinkRules(sinkRules, GoRuleConditionRewriter(callExpr, statement, returnValue), factReader, markAfterAnyAccessorResolver)
    }

    override fun propagateUnresolvedCallFact(
        factAp: FinalFactAp,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo?) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit
    ) {
        propagateDefault(factAp, addCallToReturn)

        val factReader = FinalFactReader(factAp, apManager)

        val signature = callSignature ?: return
        val passRules = rulesProvider.passThroughRulesForCall(signature)

        factAp.mapCall2Start { callerFact, startFactBase ->
            val passFactReader = FinalFactReader(callerFact.rebase(startFactBase), apManager)

            val passEvaluator = TaintPassActionEvaluator(
                apManager, FactTypeChecker.Dummy, passFactReader, DummyPositionTypeResolver
            )

            val passThroughFacts = passRules.maybeFlatMap { item ->
                item.actionsAfter.maybeFlatMap {
                    passEvaluator.accept(item, it)
                }
            }

            if (startFactBase !is AccessPathBase.ClassStatic) {
                context.taint.externalMethodTracker?.trackExternalMethod(
                    method = signature.name,
                    signature = "args:${signature.arity}",
                    factPosition = startFactBase.toString(),
                    rulesApplied = passThroughFacts.isSome,
                )
            }

            passThroughFacts.onSome { evaluatedPass ->
                evaluatedPass.forEach { evp ->
                    val rewrittenFacts = summaryRewriter.rewriteSummaryFact(evp.fact)
                    for ((unrefinedFact, factRefinement) in rewrittenFacts) {
                        val fact = factRefinement.refineFact(unrefinedFact)
                        passFactReader.updateRefinement(factRefinement)

                        val mappedFact = fact.mapExitToReturnFact() ?: continue

                        val trace = TraceInfo.Rule(evp.rule, evp.action)
                        mappedFact.forEachFactWithAliases(factAp) {
                            addCallToReturn(passFactReader, it, trace)
                        }
                    }
                }
            }

            factReader.updateRefinement(passFactReader)
        }

        if (factReader.hasRefinement) {
            addSideEffectRequirement(factReader)
        }
    }

    private fun propagateDefault(
        factAp: FinalFactAp,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo?) -> Unit
    ) {
        summaryRewriter.rewriteSummaryFact(factAp).forEach { (fact, reader) ->
            addCallToReturn(reader, fact, null)
        }
    }

    object DummyPositionTypeResolver : PositionTypeResolver {
        override fun resolve(position: PositionAccess): CommonType? = null
    }

    private fun FinalFactAp.mapExitToReturnFact(): FinalFactAp? =
        mapMethodExitToReturnFlowFact(statement, this, FactTypeChecker.Dummy).singleOrNull()

    private fun FinalFactAp.mapCall2Start(body: (FinalFactAp, AccessPathBase) -> Unit) {
        mapMethodCallToStartFlowAnyFact(
            statement,
            callExpr,
            this,
        ) { fact, startBase ->
            body(fact, startBase)
        }
    }

    private inline fun FinalFactAp.forEachSourceFactWithAliases(crossinline body: (FinalFactAp) -> Unit) =
        forEachFactWithAliases(originalFact = null, body)

    private inline fun FinalFactAp.forEachFactWithAliases(originalFact: FinalFactAp?,  crossinline body: (FinalFactAp) -> Unit) {
        body(this)

        if (originalFact != null && originalFact == this) {
            return
        }

        context.aliasAnalysis.forEachAliasAtStatement(statement, this) { aliased ->
            body(aliased)
        }
    }
}
