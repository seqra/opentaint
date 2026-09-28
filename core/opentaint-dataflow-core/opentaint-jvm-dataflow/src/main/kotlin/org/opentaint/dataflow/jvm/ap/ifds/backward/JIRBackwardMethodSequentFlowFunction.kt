package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAssignTransfer
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRSequentEdge
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.jvm.graph.JMethodEnterInst

class JIRBackwardMethodSequentFlowFunction(
    private val apManager: ApManager,
    private val analysisContext: JIRBackwardMethodAnalysisContext,
    private val currentInst: JIRInst,
) : MethodSequentFlowFunction {
    private val rules by lazy { JIRBackwardTaintRules(apManager, analysisContext) }
    private val assignTransfer = JIRAssignTransfer(JIRAssignTransfer.Direction.BACKWARD, analysisContext, currentInst)

    override fun propagateZeroToZero(): Set<Sequent> = buildSet {
        add(Sequent.ZeroToZero)
        rules.registerPrescanStatementSources(currentInst)

        val demands = when (currentInst) {
            is JIRReturnInst -> rules.methodExitSinkDemands(currentInst)
            is JMethodEnterInst -> rules.methodEntrySinkDemands(currentInst)
            else -> emptyList()
        }

        rules.recordSinkDemands(currentInst, demands).forEach { seed ->
            add(Sequent.ZeroToFact(seed, TraceInfo.Flow))
        }
    }

    override fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<Sequent> = buildSet {
        propagate(JIRSequentEdge.ZeroToFact(this, currentFactAp))
    }

    override fun propagateFactToFact(initialFactAp: InitialFactAp, currentFactAp: FinalFactAp): Set<Sequent> =
        buildSet {
            propagate(JIRSequentEdge.FactToFact(this, initialFactAp, currentFactAp))
        }

    override fun propagateNDFactToFact(initialFacts: Set<InitialFactAp>, currentFactAp: FinalFactAp): Set<Sequent> =
        buildSet {
            propagate(JIRSequentEdge.NDFactToFact(this, initialFacts, currentFactAp))
        }

    private fun JIRSequentEdge.keep(fact: FinalFactAp) {
        if (fact == current) unchanged() else propagate(fact)
    }

    private fun JIRSequentEdge.keepAll(facts: List<FinalFactAp>, vararg readers: FinalFactReader?) {
        val refinement = readers.fold<FinalFactReader?, ExclusionSet>(ExclusionSet.Empty) { refinement, reader ->
            reader?.let { refinement.union(it.getRefinement()) } ?: refinement
        }

        if (refinement is ExclusionSet.Empty) {
            facts.forEach { keep(it) }
        } else {
            facts.forEach { propagateRefined(refinement, it) }
            if (facts.isEmpty()) requireRefinement(refinement)
        }
    }

    private fun propagate(edge: JIRSequentEdge) {
        val fact = edge.current
        when (currentInst) {
            is JIRAssignInst -> assign(currentInst, edge)
            is JIRReturnInst -> methodExit(currentInst, fact, edge)
            is JIRThrowInst -> {
                val value = accessPathBase(currentInst.throwable)
                val keep: (FinalFactAp) -> Unit = { edge.keep(it) }
                assignTransfer.assignBase(AccessPathBase.Exception, value, fact, keep, keep)
            }

            is JMethodEnterInst -> methodEnter(fact, edge)
            else -> edge.unchanged()
        }
    }

    private fun methodExit(inst: JIRReturnInst, fact: FinalFactAp, edge: JIRSequentEdge) {
        val requirementReader = rules.matchEndRequirement(inst, fact)
        val sources = rules.matchMethodExitSources(inst, fact)
        rules.recordSourceMatches(inst, sources)

        val demands = mutableListOf<FinalFactAp>()
        val returnBase = inst.returnValue?.let { accessPathBase(it) }
        assignTransfer.assignBase(AccessPathBase.Return, returnBase, fact, demands::add, demands::add)
        demands += sources.conditionDemands

        edge.keepAll(demands, sources.reader, requirementReader)
    }

    private fun methodEnter(fact: FinalFactAp, edge: JIRSequentEdge) {
        val requirementReader = rules.matchEndRequirement(currentInst, fact)
        val sources = rules.matchMethodEntrySources(currentInst, fact)
        rules.recordMethodEntrySourceMatches(currentInst, sources, edge.initialFacts)

        val demands = if (edge.initialFacts.isEmpty() && !rules.keepsZeroEdgeDemandsAtMethodEnter(currentInst)) {
            emptyList()
        } else {
            listOf(fact) + sources.conditionDemands
        }
        edge.keepAll(demands, sources.reader, requirementReader)
    }

    private fun assign(inst: JIRAssignInst, edge: JIRSequentEdge) {
        assignTransfer.assign(inst, edge) { demand, staticFact ->
            val sources = rules.matchStaticFieldSources(inst, demand)
            rules.recordSourceMatches(inst, sources)
            edge.keepAll(listOf(staticFact) + sources.conditionDemands, sources.reader)
        }
    }
}
