package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoFlowFunctionUtils.resolvePosAccess
import org.opentaint.dataflow.go.GoMethodCallFactMapper
import org.opentaint.dataflow.go.GoMethodCallFactMapper.mapMethodExitToReturnFlowFact
import org.opentaint.dataflow.go.rules.GoAssignMark
import org.opentaint.dataflow.go.rules.GoRuleCondition
import org.opentaint.dataflow.go.rules.TaintRules
import org.opentaint.dataflow.taint.FactReader
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.FinalFactReaderWithPrefix
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.TaintSourceActionEvaluator
import org.opentaint.dataflow.taint.TaintUtil
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRValue
import org.opentaint.util.onSome

class GoMethodCallTaintUtil(
    private val statement: GoIRInst,
    private val callExpr: GoCallExpr,
    val returnValue: GoIRValue?,
    private val context: GoMethodAnalysisContext,
    apManager: ApManager
) : TaintUtil<GoRuleCondition, TaintRules.Source, TaintRules.Sink, TraceInfo>(apManager) {
    private val sinkTracker get() = context.taint.taintSinkTracker

    override fun TaintRules.Source.srcCondition(): CommonCondition<GoRuleCondition> = condition
    override fun TaintRules.Sink.sinkCondition(): CommonCondition<GoRuleCondition> = condition

    override fun sourceAssumptionsManager(): RuleAssumptionsManager<TaintRules.Source> =
        object : RuleAssumptionsManager<TaintRules.Source> {
            override fun storeAssumptions(
                rule: TaintRules.Source,
                assumptions: Map<InitialFactAp, Set<InitialFactAp>>
            ) {
                sinkTracker.addSourceRuleAssumptions(rule, statement, assumptions)
            }

            override fun currentAssumptions(rule: TaintRules.Source): Set<InitialFactAp> =
                sinkTracker.currentSourceRuleAssumptions(rule, statement)

            override fun currentAssumptionPreconditions(
                rule: TaintRules.Source,
                assumptions: List<InitialFactAp>
            ) = sinkTracker.currentSourceRuleAssumptionsPreconditions(rule, statement, assumptions)
        }

    override fun sinkAssumptionsManager(): RuleAssumptionsManager<TaintRules.Sink> =
        object : RuleAssumptionsManager<TaintRules.Sink> {
            override fun storeAssumptions(
                rule: TaintRules.Sink,
                assumptions: Map<InitialFactAp, Set<InitialFactAp>>
            ) {
                sinkTracker.addSinkRuleAssumptions(rule, statement, assumptions)
            }

            override fun currentAssumptions(rule: TaintRules.Sink): Set<InitialFactAp> =
                sinkTracker.currentSinkRuleAssumptions(rule, statement)
        }

    override fun conditionFact(factReader: FinalFactReader): List<FinalFactReader> {
        val readers = mutableListOf<FinalFactReader>()
        GoMethodCallFactMapper.mapMethodCallToStartFlowFact(
            statement,
            callee = callExpr.enclosingMethod, // todo: remove hack
            callExpr,
            returnValue,
            factReader.factAp,
            FactTypeChecker.Dummy
        ) { fact, startBase ->
            readers += FinalFactReader(fact.rebase(startBase), apManager)
        }
        return readers
    }

    /**
     * Modifier-permissive sink-condition matching for Go: when a tainted value is
     * passed as a variadic-`interface{}` arg, the Go SSA wraps it in a slice
     * element, so the fact at the sink looks like `arg(N).[*]![mark].$` even
     * though the sink rule asks for `ContainsMark(arg(N))`. Without help the
     * literal-`Argument(N)` lookup misses the modifier-bearing fact.
     *
     * Mirrors `JIRMethodCallTaintUtil.arrayElementConditionReaders` — for each
     * Argument-based fact reader that actually contains an element-accessor
     * sub-fact, register an additional [FinalFactReaderWithPrefix] that exposes
     * the sub-fact "as if" it lived at `arg(N)` directly. The original reader
     * stays in the list, so non-variadic sinks keep working unchanged. The fix
     * is one-sided (sink only) — pass-through and source paths use their own
     * position-resolved evaluators where the modifier-permissive shape is
     * already covered by the bundled go-config's dual-form rules.
     */
    override fun patchSinkConditionFactReader(factReaders: List<FinalFactReader>): List<FactReader> {
        val elementWrappedReaders = factReaders.mapNotNull { reader ->
            val base = reader.factAp.base as? AccessPathBase.Argument ?: return@mapNotNull null
            val elementPosition = PositionAccess.Complex(PositionAccess.Simple(base), ElementAccessor)
            if (!reader.containsPosition(elementPosition)) return@mapNotNull null
            FinalFactReaderWithPrefix(reader, ElementAccessor)
        }
        return factReaders + elementWrappedReaders
    }

    override fun handleReachedSink(
        rule: TaintRules.Sink,
        factReader: FinalFactReader?,
        evaluatedFacts: List<InitialFactAp>
    ) {
        val factAfterSinkEvaluator by lazy {
            TaintSourceActionEvaluator(
                apManager,
                exclusion = ExclusionSet.Universe,
            )
        }

        if (evaluatedFacts.isEmpty()) {
            // unconditional sinks handled with zero fact
            if (factReader != null) return

            if (rule.trackFactsReachAnalysisEnd.isEmpty()) {
                sinkTracker.addUnconditionalVulnerability(
                    context.methodEntryPoint, statement, rule
                )
                return
            }

            val requiredEndFacts = hashSetOf<FinalFactAp>()
            applySourceAction(rule, rule.trackFactsReachAnalysisEnd, factAfterSinkEvaluator) { f ->
                requiredEndFacts += f
            }

            sinkTracker.addUnconditionalVulnerabilityWithEndFactRequirement(
                context.methodEntryPoint, statement, rule, requiredEndFacts
            )
            return
        }

        val mappedFacts = evaluatedFacts.mapTo(hashSetOf()) {
            it.mapExitToReturnFact() ?: error("Fact mapping failure")
        }

        if (rule.trackFactsReachAnalysisEnd.isEmpty()) {
            sinkTracker.addVulnerability(
                context.methodEntryPoint, mappedFacts, statement, rule
            )
            return
        }

        val requiredEndFacts = hashSetOf<FinalFactAp>()
        applySourceAction(rule, rule.trackFactsReachAnalysisEnd, factAfterSinkEvaluator) { f ->
            requiredEndFacts += f
        }

        sinkTracker.addVulnerabilityWithEndFactRequirement(
            context.methodEntryPoint, mappedFacts, statement, rule, requiredEndFacts
        )
    }

    override fun applySourceAction(
        rule: TaintRules.Source,
        sourceEvaluator: TaintSourceActionEvaluator,
        createFinalFact: (FinalFactAp, TraceInfo) -> Unit
    ) = applySourceAction(rule, rule.actionsAfter, sourceEvaluator) { f ->
        createFinalFact(f, TraceInfo.Flow)
    }

    private inline fun applySourceAction(
        rule: CommonTaintConfigurationItem,
        actions: List<GoAssignMark>,
        sourceEvaluator: TaintSourceActionEvaluator,
        createFinalFact: (FinalFactAp) -> Unit,
    ) {
        for (action in actions) {
            val position = action.pos.resolvePosAccess()
            sourceEvaluator.evaluate(rule, action, position, TaintMarkAccessor(action.mark)).onSome { facts ->
                facts.forEach { f ->
                    f.mapExitToReturnFact()?.let { createFinalFact(f) }
                }
            }
        }
    }

    private fun FinalFactAp.mapExitToReturnFact(): FinalFactAp? =
        mapMethodExitToReturnFlowFact(statement, this, FactTypeChecker.Dummy).singleOrNull()

    private fun InitialFactAp.mapExitToReturnFact(): InitialFactAp? =
        mapMethodExitToReturnFlowFact(statement, this).singleOrNull()
}
