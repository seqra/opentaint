package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
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
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.Unchanged
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.ZeroCallFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.ZeroCallFailureFact
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoMethodCallFactMapper
import org.opentaint.dataflow.go.GoMethodCallFactMapper.factIsRelevantToMethodCall
import org.opentaint.dataflow.go.GoMethodCallFactMapper.mapMethodExitToReturnFlowFact
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRValue

/**
 * Handles interprocedural taint propagation at call sites:
 * source rule application, sink rule checking, pass-through rules, and fact mapping.
 */
class GoMethodCallFlowFunction(
    private val apManager: ApManager,
    private val context: GoMethodAnalysisContext,
    private val returnValueFromFramework: GoIRValue?,
    private val callExpr: GoCallExpr,
    private val statement: GoIRInst,
    private val generateTrace: Boolean,
) : MethodCallFlowFunction {

    private val method: GoIRFunction get() = context.method
    private val rulesProvider get() = context.taint.taintConfig
    private val calleeName: String? get() = callExpr.calleeName

    /**
     * Get the return value register. GoIRCall doesn't implement CommonAssignInst,
     * so the framework passes null for returnValue. We extract it directly from the statement.
     */
    private val returnValue: GoIRValue?
        get() = returnValueFromFramework ?: GoFlowFunctionUtils.extractResultRegister(statement)

    // ── Zero propagation ─────────────────────────────────────────────

    override fun propagateZeroToZero(): Set<ZeroCallFact> {
        val result = mutableSetOf(
            CallToReturnZeroFact,
            CallToStartZeroFact,
        )
        applySourceRules(result)
        return result
    }

    override fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<ZeroCallFact> = buildSet {
        propagateFact(
            factAp = currentFactAp,
            skipCall = { this += Unchanged },
            addCallToReturn = { factAp, trace -> this += CallToReturnZFact(factAp, trace) },
            addCallToStart = { callerFact, startBase, trace -> this += CallToStartZFact(callerFact, startBase, trace) },
        )
    }

    // ── Fact propagation ─────────────────────────────────────────────

    override fun propagateFactToFact(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
    ): Set<FactCallFact> = buildSet {
        propagateFact(
            factAp = currentFactAp,
            skipCall = { this += Unchanged },
            addCallToReturn = { factAp, trace ->
                this += CallToReturnFFact(initialFactAp.replaceExclusions(factAp.exclusions), factAp, trace)
            },
            addCallToStart = { callerFact, startBase, trace ->
                this += CallToStartFFact(initialFactAp.replaceExclusions(callerFact.exclusions), callerFact, startBase, trace)
            },
        )
    }

    override fun propagateNDFactToFact(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
    ): Set<NDFactCallFact> {
        return setOf(Unchanged)
    }

    private fun propagateFact(
        factAp: FinalFactAp,
        skipCall: () -> Unit,
        addCallToReturn: (FinalFactAp, TraceInfo) -> Unit,
        addCallToStart: (callerFact: FinalFactAp, startBase: AccessPathBase, TraceInfo) -> Unit,
    ) {
        // 0. Relevance check
        if (!factIsRelevantToMethodCall(statement, returnValue as? CommonValue, callExpr, factAp)) {
            skipCall()
            return
        }

        GoMethodCallFactMapper.mapMethodCallToStartFlowFact(
            statement,
            callee = method, // todo: remove hack
            callExpr,
            returnValue,
            factAp,
            FactTypeChecker.Dummy
        ) { fact, startBase ->
            // 1. Sink rules
            applySinkRules(fact, startBase, addCallToReturn)

            // 2. Pass-through rules
            addCallToStart(fact, startBase, TraceInfo.Flow)
        }
    }

    // ── Source rule application (zero-to-zero only) ──────────────────

    private fun applySourceRules(result: MutableSet<ZeroCallFact>) {
        val name = calleeName ?: return
        val sourceRules = rulesProvider.sourceRulesForCall(name)

        for (rule in sourceRules) {
            val base = GoFlowFunctionUtils.resolvePosition(rule.pos)

            val factAp = apManager.createFinalAp(base, ExclusionSet.Universe)
                .prependAccessor(TaintMarkAccessor(rule.mark))

            val callerFacts = mapMethodExitToReturnFlowFact(statement, factAp, FactTypeChecker.Dummy)

            val traceInfo = if (generateTrace) TraceInfo.Flow else null
            callerFacts.mapTo(result) {
                CallToReturnZFact(it, traceInfo)
            }
        }
    }

    // ── Sink rule application ────────────────────────────────────────

    private fun applySinkRules(
        currentFactAp: FinalFactAp,
        startBase: AccessPathBase,
        addCallToReturn: (FinalFactAp, TraceInfo) -> Unit,
    ) {
        val name = calleeName ?: return
        val sinkRules = rulesProvider.sinkRulesForCall(name)

        for (rule in sinkRules) {
            val sinkArgBase = GoFlowFunctionUtils.resolvePosition(rule.pos)
            if (sinkArgBase != startBase) continue

            val markAccessor = TaintMarkAccessor(rule.mark)
            if (currentFactAp.startsWithAccessor(markAccessor)) {
                context.taint.taintSinkTracker.addVulnerability(
                    methodEntryPoint = context.methodEntryPoint,
                    facts = emptySet(), // todo: vulnerability facts
                    statement = statement,
                    rule = rule,
                )
            } else if (currentFactAp.isAbstract() && !currentFactAp.exclusions.contains(markAccessor)) {
                // Trigger refinement
                val refinedFact = currentFactAp.exclude(markAccessor)
                addCallToReturn(refinedFact, TraceInfo.Flow)
            }
        }
    }

    override fun propagateZeroToZeroResolutionFailure(): Set<ZeroCallFailureFact> =
        setOf(CallToReturnZeroFact)

    override fun propagateZeroToFactResolutionFailure(
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): Set<ZeroCallFailureFact> = buildSet {
        applyPassRules(currentFactAp, startFactBase)
            .mapTo(this) { CallToReturnZFact(it, traceInfo = null) }

        this += CallToReturnZFact(currentFactAp, traceInfo = null)
    }

    override fun propagateFactToFactResolutionFailure(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): Set<FactCallFailureFact> = buildSet {
        applyPassRules(currentFactAp, startFactBase)
            .mapTo(this) { CallToReturnFFact(initialFactAp, it, traceInfo = null) }

        this += CallToReturnFFact(initialFactAp, currentFactAp, traceInfo = null)
    }

    private fun applyPassRules(
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): List<FinalFactAp> {
        val name = calleeName ?: return emptyList()
        val passRules = rulesProvider.passRulesForCall(name)

        val result = mutableListOf<FinalFactAp>()
        for (rule in passRules) {
            val (fromBase, fromAccessors) = GoFlowFunctionUtils.resolvePositionWithModifiers(rule.from)
            if (startFactBase != fromBase) continue

            val (toBase, toAccessors) = GoFlowFunctionUtils.resolvePositionWithModifiers(rule.to)

            if (fromAccessors.isNotEmpty()) {
                TODO("Complex from")
            }

            var newFact = currentFactAp.rebase(toBase)
            for (accessor in toAccessors) {
                newFact = newFact.prependAccessor(accessor)
            }

            result += mapMethodExitToReturnFlowFact(statement, newFact, FactTypeChecker.Dummy)
        }
        return result
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
}
