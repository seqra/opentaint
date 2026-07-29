package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnFFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnNonDistributiveFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.Unchanged
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodCallFactMapper
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate

/**
 * Call-to-return flow for call-like expressions that do not invoke a method.
 *
 * Lambda expressions construct an object. An invokedynamic bootstrap links its call site instead
 * of being invoked by the program. Neither expression has a callee to analyze or match against
 * method rules, summaries, and approximations.
 */
class JIRNonMethodCallFlowFunction(
    private val returnValue: JIRImmediate?,
    private val callExpr: JIRCallExpr,
) : MethodCallFlowFunction {
    override fun propagateZeroToZero(): Set<MethodCallFlowFunction.ZeroCallFact> =
        setOf(CallToReturnZeroFact)

    override fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<MethodCallFlowFunction.ZeroCallFact> =
        if (isRelevant(currentFactAp)) {
            setOf(CallToReturnZFact(currentFactAp, TraceInfo.Flow))
        } else {
            setOf(Unchanged)
        }

    override fun propagateFactToFact(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
    ): Set<MethodCallFlowFunction.FactCallFact> =
        if (isRelevant(currentFactAp)) {
            setOf(CallToReturnFFact(initialFactAp, currentFactAp, TraceInfo.Flow))
        } else {
            setOf(Unchanged)
        }

    override fun propagateNDFactToFact(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
    ): Set<MethodCallFlowFunction.NDFactCallFact> =
        if (isRelevant(currentFactAp)) {
            setOf(CallToReturnNonDistributiveFact(initialFacts, currentFactAp, TraceInfo.Flow))
        } else {
            setOf(Unchanged)
        }

    override fun propagateZeroToZeroResolutionFailure(): Set<MethodCallFlowFunction.ZeroCallFailureFact> =
        setOf(CallToReturnZeroFact)

    override fun propagateZeroToFactResolutionFailure(
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase,
    ): Set<MethodCallFlowFunction.ZeroCallFailureFact> =
        setOf(CallToReturnZFact(currentFactAp, TraceInfo.Flow))

    override fun propagateFactToFactResolutionFailure(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase,
    ): Set<MethodCallFlowFunction.FactCallFailureFact> =
        setOf(CallToReturnFFact(initialFactAp, currentFactAp, TraceInfo.Flow))

    override fun propagateNDFactToFactResolutionFailure(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase,
    ): Set<MethodCallFlowFunction.NDFactCallFailureFact> =
        setOf(CallToReturnNonDistributiveFact(initialFacts, currentFactAp, TraceInfo.Flow))

    private fun isRelevant(fact: FactAp): Boolean =
        JIRMethodCallFactMapper.factIsRelevantToMethodCall(returnValue, callExpr, fact.base)
}
