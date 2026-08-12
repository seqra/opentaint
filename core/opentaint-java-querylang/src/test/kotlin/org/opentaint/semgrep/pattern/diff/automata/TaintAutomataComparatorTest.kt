package org.opentaint.semgrep.pattern.diff.automata

import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureName
import org.opentaint.semgrep.pattern.conversion.automata.MethodEnclosingClassName
import org.opentaint.semgrep.pattern.conversion.automata.MethodFormulaManager
import org.opentaint.semgrep.pattern.conversion.automata.MethodName
import org.opentaint.semgrep.pattern.conversion.automata.MethodSignature
import org.opentaint.semgrep.pattern.conversion.automata.Predicate
import org.opentaint.semgrep.pattern.conversion.taint.MetaVarConstraintOrPlaceHolder
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataEdges
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.Edge
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.EdgeCondition
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.EdgeEffect
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.MethodPredicate
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.State
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata.StateRegister
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleEdge
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleGenerationMetaVarInfo
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertTrue

class TaintAutomataComparatorTest {
    private val comparator = TaintAutomataComparator()

    @Test
    fun generatedStateAndRegisterEpochIdsAreAlphaEquivalent() {
        val x = MetavarAtom.create("\$X")
        val oldInitial = state(10, x to 10)
        val oldAccept = state(11, x to 11)
        val newInitial = state(100, x to 100)
        val newAccept = state(101, x to 101)
        val edge = methodCall(
            reads = mapOf(x to listOf(methodPredicate("source"))),
            assigns = mapOf(x to listOf(methodPredicate("source"))),
        )

        val old = taintEdges(automata(oldInitial, setOf(oldAccept), transitions = listOf(Arc(oldInitial, edge, oldAccept))))
        val new = taintEdges(automata(newInitial, setOf(newAccept), transitions = listOf(Arc(newInitial, edge, newAccept))))

        assertEquals(TaintAutomataComparison.Equivalent, comparator.compare(old, new))
    }

    @Test
    fun differentUserMetavariableNamesAreNotAlphaEquivalent() {
        val x = MetavarAtom.create("\$X")
        val y = MetavarAtom.create("\$Y")
        val old = taintEdges(automata(state(0, x to 0)))
        val new = taintEdges(automata(state(50, y to 50)))

        val result = assertIs<TaintAutomataComparison.Different>(comparator.compare(old, new))

        assertTrue(result.witnesses.all { it.observation == AutomataTraceObservation.TRANSITION })
        assertEquals(AutomataTraceDirection.entries.toSet(), result.witnesses.map { it.direction }.toSet())
    }

    @Test
    fun conditionChangeProducesDirectionalTraceWitnesses() {
        val oldInitial = state(0)
        val oldAccept = state(1)
        val newInitial = state(20)
        val newAccept = state(21)
        val old = taintEdges(
            automata(oldInitial, setOf(oldAccept), transitions = listOf(Arc(oldInitial, methodCall("oldName"), oldAccept)))
        )
        val new = taintEdges(
            automata(newInitial, setOf(newAccept), transitions = listOf(Arc(newInitial, methodCall("newName"), newAccept)))
        )

        val result = assertIs<TaintAutomataComparison.Different>(comparator.compare(old, new))

        assertEquals(AutomataTraceDirection.entries.toSet(), result.witnesses.map { it.direction }.toSet())
        assertTrue(result.witnesses.all { it.steps.size == 1 })
        assertTrue(result.witnesses.all { it.observation == AutomataTraceObservation.TRANSITION })
    }

    @Test
    fun terminalDifferenceUsesTheSynchronousPrefix() {
        val oldInitial = state(0)
        val oldFinal = state(1)
        val newInitial = state(10)
        val newFinal = state(11)
        val edge = methodCall("same")
        val old = taintEdges(
            automata(oldInitial, accepts = setOf(oldFinal), transitions = listOf(Arc(oldInitial, edge, oldFinal)))
        )
        val new = taintEdges(
            automata(newInitial, transitions = listOf(Arc(newInitial, edge, newFinal)))
        )

        val result = assertIs<TaintAutomataComparison.Different>(comparator.compare(old, new))
        val witness = result.witnesses.single()

        assertEquals(AutomataTraceDirection.OLD_ONLY, witness.direction)
        assertEquals(AutomataTraceObservation.ACCEPT, witness.observation)
        assertEquals(1, witness.steps.size)
    }

    @Test
    fun generatedEdgeProjectionIsComparedAfterGraphTransition() {
        val oldInitial = state(0)
        val oldAccept = state(1)
        val newInitial = state(10)
        val newAccept = state(11)
        val edge = methodCall("same")
        val oldAutomata = automata(oldInitial, setOf(oldAccept), transitions = listOf(Arc(oldInitial, edge, oldAccept)))
        val newAutomata = automata(newInitial, setOf(newAccept), transitions = listOf(Arc(newInitial, edge, newAccept)))
        val generated = TaintRuleEdge(
            oldInitial,
            oldAccept,
            checkGlobalState = true,
            edge.condition,
            edge.effect,
            TaintRuleEdge.Kind.MethodCall,
        )

        val result = assertIs<TaintAutomataComparison.Different>(
            comparator.compare(taintEdges(oldAutomata, ordinary = listOf(generated)), taintEdges(newAutomata))
        )

        assertEquals(AutomataTraceDirection.OLD_ONLY, result.witnesses.single().direction)
        assertEquals(AutomataTraceObservation.GENERATED_EDGE, result.witnesses.single().observation)
    }

    @Test
    fun strictMetavariableConstraintKeysAreCompared() {
        val automata = automata(state(0))
        val old = taintEdges(
            automata,
            metaVarInfo = TaintRuleGenerationMetaVarInfo(
                mapOf("\$X" to MetaVarConstraintOrPlaceHolder.PlaceHolder(null))
            ),
        )
        val new = taintEdges(
            automata,
            metaVarInfo = TaintRuleGenerationMetaVarInfo(
                mapOf("\$Y" to MetaVarConstraintOrPlaceHolder.PlaceHolder(null))
            ),
        )

        val result = assertIs<TaintAutomataComparison.Different>(comparator.compare(old, new))

        assertEquals(AutomataTraceDirection.entries.toSet(), result.witnesses.map { it.direction }.toSet())
        assertTrue(result.witnesses.all { it.observation == AutomataTraceObservation.METAVAR_INFO })
    }

    @Test
    fun sameExactLabelWithMultipleDestinationsIsInconclusive() {
        val initial = state(0)
        val first = state(1)
        val second = state(2)
        val edge = methodCall("same")
        val nondeterministic = taintEdges(
            automata(
                initial,
                accepts = setOf(first, second),
                transitions = listOf(Arc(initial, edge, first), Arc(initial, edge, second)),
            )
        )

        val result = assertIs<TaintAutomataComparison.Inconclusive>(comparator.compare(nondeterministic, nondeterministic))

        assertEquals(
            AutomataInconclusiveReason.UNSUPPORTED_NONDETERMINISTIC_REGISTER_AUTOMATON,
            result.reason,
        )
    }

    @Test
    fun productLimitIsReportedAsInconclusive() {
        val oldInitial = state(0)
        val oldNext = state(1)
        val newInitial = state(10)
        val newNext = state(11)
        val edge = methodCall("same")
        val old = taintEdges(automata(oldInitial, transitions = listOf(Arc(oldInitial, edge, oldNext))))
        val new = taintEdges(automata(newInitial, transitions = listOf(Arc(newInitial, edge, newNext))))
        val limited = TaintAutomataComparator(TaintAutomataComparisonLimits(maxProductConfigurations = 1))

        val result = assertIs<TaintAutomataComparison.Inconclusive>(limited.compare(old, new))

        assertEquals(AutomataInconclusiveReason.PRODUCT_LIMIT_REACHED, result.reason)
    }

    private fun state(id: Int, vararg registers: Pair<MetavarAtom, Int>) =
        State(id, StateRegister(mapOf(*registers)))

    private fun methodCall(name: String): Edge.MethodCall = methodCall(
        other = listOf(methodPredicate(name)),
    )

    private fun methodCall(
        reads: Map<MetavarAtom, List<MethodPredicate>> = emptyMap(),
        other: List<MethodPredicate> = emptyList(),
        assigns: Map<MetavarAtom, List<MethodPredicate>> = emptyMap(),
    ) = Edge.MethodCall(EdgeCondition(reads, other), EdgeEffect(assigns))

    private fun methodPredicate(name: String) = MethodPredicate(
        Predicate(
            MethodSignature(
                MethodName(SignatureName.Concrete(name)),
                MethodEnclosingClassName.anyClassName,
            ),
            constraint = null,
        ),
        negated = false,
    )

    private fun automata(
        initial: State,
        accepts: Set<State> = emptySet(),
        dead: Set<State> = emptySet(),
        transitions: List<Arc> = emptyList(),
    ) = TaintRegisterStateAutomata(
        MethodFormulaManager(),
        initial,
        accepts,
        dead,
        transitions.groupBy(Arc::source).mapValues { (_, arcs) -> arcs.map { it.edge to it.destination }.toSet() },
    )

    private fun taintEdges(
        automata: TaintRegisterStateAutomata,
        ordinary: List<TaintRuleEdge> = emptyList(),
        finalAccept: List<TaintRuleEdge> = emptyList(),
        finalDead: List<TaintRuleEdge> = emptyList(),
        metaVarInfo: TaintRuleGenerationMetaVarInfo = TaintRuleGenerationMetaVarInfo(emptyMap()),
    ) = TaintAutomataEdges(
        automata,
        metaVarInfo,
        globalStateAssignStates = emptySet(),
        edges = ordinary,
        edgesToFinalAccept = finalAccept,
        edgesToFinalDead = finalDead,
    )

    private data class Arc(val source: State, val edge: Edge, val destination: State)
}
