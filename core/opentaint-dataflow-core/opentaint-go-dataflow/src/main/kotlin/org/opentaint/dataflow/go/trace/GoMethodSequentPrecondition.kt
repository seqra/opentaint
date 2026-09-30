package org.opentaint.dataflow.go.trace

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition
import org.opentaint.dataflow.go.analysis.GoMethodAnalysisContext
import org.opentaint.dataflow.go.analysis.GoStatementSummary
import org.opentaint.dataflow.go.analysis.applyGlobalOrFieldReadSourceRules
import org.opentaint.dataflow.taint.InitialFactReader
import org.opentaint.dataflow.taint.TaintSourceActionPreconditionEvaluator
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRInst

class GoMethodSequentPrecondition(
    private val apManager: ApManager,
    private val currentInst: GoIRInst,
    private val analysisContext: GoMethodAnalysisContext,
) : MethodSequentPrecondition {
    private val summary: StatementSummary by lazy {
        GoStatementSummary.buildReversed(apManager, currentInst, analysisContext.method, analysisContext.aliasAnalysis)
    }

    private val forwardSummary: StatementSummary by lazy {
        GoStatementSummary.build(apManager, currentInst, analysisContext.method, analysisContext.aliasAnalysis)
    }

    override fun factPrecondition(fact: InitialFactAp): Set<SequentPrecondition> {
        val result = hashSetOf<SequentPrecondition>()
        summary.preconditions(fact)?.let { result.addFactPreconditions(fact, it) }
        result.unconditionalGlobalOrFieldReadSourceRulePrecondition(fact)
        return result.ifEmpty { setOf(SequentPrecondition.Unchanged) }
    }

    private fun MutableSet<SequentPrecondition>.addFactPreconditions(
        fact: InitialFactAp,
        preconditions: List<InitialFactAp>,
    ) {
        if (forwardSummary.find(fact.base) != null) {
            this += PreconditionFactsForInitialFact(fact, preconditions)
            return
        }

        this += SequentPrecondition.Unchanged
        val aliasPreconditions = preconditions.filter { it.base != fact.base }
        if (aliasPreconditions.isNotEmpty()) {
            this += PreconditionFactsForInitialFact(fact, aliasPreconditions)
        }
    }

    private fun MutableSet<SequentPrecondition>.unconditionalGlobalOrFieldReadSourceRulePrecondition(
        fact: InitialFactAp,
    ) {
        val inst = currentInst as? GoIRAssignInst ?: return
        val lhv = AccessPathBase.LocalVar(inst.register.index)
        if (fact.base != lhv) return

        applyGlobalOrFieldReadSourceRules(
            currentInst, analysisContext,
            mkSourceEvaluator = {
                val entryFactReader = InitialFactReader(fact.rebase(AccessPathBase.Return), apManager)
                TaintSourceActionPreconditionEvaluator(entryFactReader)
            }
        ) { rule, action, _, _ ->
            this += MethodSequentPrecondition.SequentSource(
                fact, TaintRulePrecondition.Source(rule, setOf(action)),
            )
        }
    }
}
