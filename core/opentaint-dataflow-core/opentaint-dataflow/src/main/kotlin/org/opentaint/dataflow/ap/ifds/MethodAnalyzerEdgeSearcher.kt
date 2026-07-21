package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.AnalysisManager
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPreconditionFacts
import org.opentaint.dataflow.graph.MethodInstGraph
import org.opentaint.ir.api.common.cfg.CommonAssignInst
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonValue

abstract class MethodAnalyzerEdgeSearcher(
    private val edges: MethodAnalyzerEdges,
    private val apManager: ApManager,
    private val analysisManager: AnalysisManager,
    private val analysisContext: MethodAnalysisContext,
    private val graph: MethodInstGraph,
) {
    abstract fun matchFact(factAtStatement: FinalFactAp, targetFactPattern: InitialFactAp): Boolean

    fun findMatchingEdgesInitialFacts(statement: CommonInst, fact: InitialFactAp): Set<Set<InitialFactAp>> {
        val matchingInitialFacts = hashSetOf<Set<InitialFactAp>>()

        val visitedStatements = hashSetOf<CommonInst>()
        val unprocessedStatements = mutableListOf(statement)

        while (unprocessedStatements.isNotEmpty()) {
            val stmt = unprocessedStatements.removeLast()
            if (!visitedStatements.add(stmt)) continue

            possiblePreconditionAtStatement(unprocessedStatements, stmt, fact).forEach { storedFact ->
                collectMatchingInitialFacts(stmt, storedFact, matchingInitialFacts)
            }
        }

        return matchingInitialFacts
    }

    private fun collectMatchingInitialFacts(
        stmt: CommonInst,
        storedFact: InitialFactAp,
        matchingInitialFacts: HashSet<Set<InitialFactAp>>,
    ) {
        if (edges.allZeroToFactFactsAtStatement(stmt, storedFact).any { matchFact(it, storedFact) }) {
            matchingInitialFacts.add(emptySet())
        }

        edges.allFactToFactFactsAtStatement(stmt, storedFact).forEach { (initialFact, finalFact) ->
            if (matchFact(finalFact, storedFact)) {
                matchingInitialFacts.add(setOf(initialFact))
            }
        }

        edges.allNDFactToFactFactsAtStatement(stmt, storedFact).forEach { (initialFacts, finalFact) ->
            if (matchFact(finalFact, storedFact)) {
                matchingInitialFacts.add(initialFacts)
            }
        }
    }

    private fun possiblePreconditionAtStatement(
        unprocessed: MutableList<CommonInst>,
        statement: CommonInst,
        fact: InitialFactAp,
    ): List<InitialFactAp> {
        var predecessorsIsEmpty = true
        val result = mutableListOf<InitialFactAp>()

        graph.forEachPredecessor(analysisManager, statement) { predecessor ->
            predecessorsIsEmpty = false

            val queryResult = factsForPrecondition(predecessor, fact)
            if (queryResult.facts != null) {
                result.addAll(queryResult.facts)
                if (!queryResult.searchNext) {
                    return@forEachPredecessor
                }
            }

            unprocessed.add(predecessor)
        }

        if (predecessorsIsEmpty) {
            result.add(fact)
        }

        return result
    }

    private data class FactQueryResult(
        val facts: List<InitialFactAp>?,
        val searchNext: Boolean,
    )

    private fun factsForPrecondition(statement: CommonInst, fact: InitialFactAp): FactQueryResult {
        val statementCall = analysisManager.getCallExpr(statement)
        if (statementCall != null) {
            val returnValue: CommonValue? = (statement as? CommonAssignInst)?.lhv

            val preconditionFunction = analysisManager.getMethodCallPrecondition(
                apManager, analysisContext, returnValue, statementCall, statement
            )

            val preconditions = preconditionFunction.factPrecondition(fact)
            return preconditions.queryResult<_, CallPrecondition.Unchanged, PreconditionFactsForInitialFact> { initialFact }
        } else {
            val preconditionFunction = analysisManager.getMethodSequentPrecondition(
                apManager, analysisContext, statement
            )
            val preconditions = preconditionFunction.factPrecondition(fact)
            return preconditions.queryResult<_, SequentPrecondition.Unchanged, SequentPreconditionFacts> { fact }
        }
    }

    private inline fun <reified T, reified U, reified F> Iterable<T>.queryResult(
        initialFact: F.() -> InitialFactAp
    ): FactQueryResult {
        val facts = mutableListOf<InitialFactAp>()
        var searchNext = false
        for (precondition in this) {
            when (precondition) {
                is U -> {
                    searchNext = true
                }

                is F -> {
                    // todo: use provided fact instead of this list?
                    facts += precondition.initialFact()
                }
            }
        }
        return FactQueryResult(facts.takeIf { it.isNotEmpty() }, searchNext)
    }
}
