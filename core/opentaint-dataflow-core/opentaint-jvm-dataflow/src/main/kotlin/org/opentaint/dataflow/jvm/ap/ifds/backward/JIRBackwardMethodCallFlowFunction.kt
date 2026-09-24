package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnNonDistributiveFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToReturnZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.CallToStartZeroFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.FactCallFailureFact
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.ZeroCallFact
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst

class JIRBackwardMethodCallFlowFunction(
    private val apManager: ApManager,
    private val analysisContext: JIRBackwardMethodAnalysisContext,
    private val returnValue: JIRImmediate?,
    private val callExpr: JIRCallExpr,
    private val statement: JIRInst,
) : MethodCallFlowFunction.Default {
    private val rules by lazy { JIRBackwardTaintRules(apManager, analysisContext) }

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
        skipCall()
    }

    override fun propagateZeroToFactResolutionFailure(
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): Set<CallToReturnZFact> {
        if (startFactBase == AccessPathBase.Return) return emptySet()
        return super.propagateZeroToFactResolutionFailure(currentFactAp, startFactBase)
    }

    override fun propagateFactToFactResolutionFailure(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): Set<FactCallFailureFact> {
        if (startFactBase == AccessPathBase.Return) return emptySet()
        return super.propagateFactToFactResolutionFailure(initialFactAp, currentFactAp, startFactBase)
    }

    override fun propagateNDFactToFactResolutionFailure(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
        startFactBase: AccessPathBase
    ): Set<CallToReturnNonDistributiveFact> {
        if (startFactBase == AccessPathBase.Return) return emptySet()
        return super.propagateNDFactToFactResolutionFailure(initialFacts, currentFactAp, startFactBase)
    }

    override fun propagateUnresolvedCallFact(
        factAp: FinalFactAp,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo?) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
    ) {
        addCallToReturn(FinalFactReader(factAp, apManager), factAp, TraceInfo.Flow)
    }
}
