package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.jvm.graph.JMethodEnterInst

class JIRBackwardMethodSequentFlowFunction(
    private val apManager: ApManager,
    private val analysisContext: JIRBackwardMethodAnalysisContext,
    private val currentInst: JIRInst,
) : MethodSequentFlowFunction {
    private val rules by lazy { JIRBackwardTaintRules(apManager, analysisContext) }

    override fun propagateZeroToZero(): Set<Sequent> = buildSet {
        add(Sequent.ZeroToZero)

        val demands = when (currentInst) {
            is JIRReturnInst -> rules.methodExitSinkDemands(currentInst)
            is JMethodEnterInst -> rules.methodEntrySinkDemands(currentInst)
            else -> emptyList()
        }

        rules.recordSinkDemands(currentInst, demands).forEach { seed ->
            add(Sequent.ZeroToFact(seed, TraceInfo.Flow))
        }
    }

    override fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<Sequent> =
        setOf(Sequent.Unchanged)

    override fun propagateFactToFact(initialFactAp: InitialFactAp, currentFactAp: FinalFactAp): Set<Sequent> =
        setOf(Sequent.Unchanged)

    override fun propagateNDFactToFact(initialFacts: Set<InitialFactAp>, currentFactAp: FinalFactAp): Set<Sequent> =
        setOf(Sequent.Unchanged)
}
