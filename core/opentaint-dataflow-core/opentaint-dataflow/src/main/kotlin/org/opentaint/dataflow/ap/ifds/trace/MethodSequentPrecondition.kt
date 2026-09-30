package org.opentaint.dataflow.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary

interface MethodSequentPrecondition {
    sealed interface SequentPrecondition {
        data object Unchanged : SequentPrecondition
    }

    sealed interface SequentPreconditionFacts: SequentPrecondition {
        val fact: InitialFactAp
    }

    data class PreconditionFactsForInitialFact(
        override val fact: InitialFactAp,
        val preconditionFacts: List<InitialFactAp>
    ): SequentPreconditionFacts

    data class SequentSource(
        override val fact: InitialFactAp,
        val rule: TaintRulePrecondition.Source
    ): SequentPreconditionFacts

    fun factPrecondition(fact: InitialFactAp): Set<SequentPrecondition>

    fun sequentPreconditions(
        forward: StatementSummary,
        reversed: StatementSummary,
        fact: InitialFactAp,
    ): Set<SequentPrecondition> {
        val facts = reversed.preconditionFacts(fact) ?: return emptySet()

        if (forward.find(fact.base) == null) {
            val otherBases = facts.filter { it.base != fact.base }
            if (otherBases.isEmpty()) return setOf(SequentPrecondition.Unchanged)
            return setOf(SequentPrecondition.Unchanged, PreconditionFactsForInitialFact(fact, otherBases))
        }

        if (facts == listOf(fact)) return emptySet()
        return setOf(PreconditionFactsForInitialFact(fact, facts))
    }
}
