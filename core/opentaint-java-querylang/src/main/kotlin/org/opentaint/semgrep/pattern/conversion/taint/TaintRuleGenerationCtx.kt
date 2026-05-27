package org.opentaint.semgrep.pattern.conversion.taint

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.util.forEach
import org.opentaint.semgrep.pattern.Mark
import org.opentaint.semgrep.pattern.Mark.RuleUniqueMarkPrefix
import org.opentaint.semgrep.pattern.UserRuleFromSemgrepInfo
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.TaintRuleStrategy
import java.util.BitSet

data class TaintRuleGenerationCtx<Item, Cond, Assign, Clean>(
    val prefix: RuleUniqueMarkPrefix,
    private val automataEdges: TaintAutomataEdges,
    private val compositionStrategy: CompositionStrategy<Item, Cond, Assign, Clean>?,
    val taintRuleStrategy: TaintRuleStrategy<Item, Cond, Assign, Clean>
) {
    interface CompositionStrategy<Item, Cond, Assign, Clean> {
        fun stateContains(
            state: TaintRegisterStateAutomata.State,
            varName: MetavarAtom,
            pos: PositionBaseWithModifiers
        ): Cond? = null

        fun stateAssign(
            state: TaintRegisterStateAutomata.State,
            varName: MetavarAtom,
            pos: PositionBaseWithModifiers
        ): List<Assign>? = null

        fun stateClean(
            state: TaintRegisterStateAutomata.State,
            stateBefore: TaintRegisterStateAutomata.State,
            varName: MetavarAtom?,
            pos: PositionBaseWithModifiers?
        ): List<Clean>? = null

        fun stateAccessedMarks(
            state: TaintRegisterStateAutomata.State,
            varName: MetavarAtom
        ): Set<Mark.GeneratedMark>? = null
    }

    val automata: TaintRegisterStateAutomata get() = automataEdges.automata
    val metaVarInfo: TaintRuleGenerationMetaVarInfo get() = automataEdges.metaVarInfo
    val globalStateAssignStates: Set<TaintRegisterStateAutomata.State> get() = automataEdges.globalStateAssignStates
    val edges: List<TaintRuleEdge> get() = automataEdges.edges
    val edgesToFinalAccept: List<TaintRuleEdge> get() = automataEdges.edgesToFinalAccept
    val edgesToFinalDead: List<TaintRuleEdge> get() = automataEdges.edgesToFinalDead

    fun globalStateMarkName(state: TaintRegisterStateAutomata.State): Mark.GeneratedMark {
        val stateId = automata.stateId(state)
        return prefix.artificialState("$stateId")
    }

    val stateVarPosition by lazy {
        PositionBase.ClassStatic(prefix.artificialState("pos").taintMarkStr()).base()
    }

    fun stateAssignMark(
        varName: MetavarAtom,
        state: TaintRegisterStateAutomata.State,
        position: PositionBaseWithModifiers
    ): List<Assign> {
        compositionStrategy?.stateAssign(state, varName, position)?.let { return it }

        val markName = stateMarkName(varName, state)
            ?: return emptyList()

        return listOf(taintRuleStrategy.createAssignMark(markName, position))
    }

    fun stateCleanMark(
        varName: MetavarAtom?,
        state: TaintRegisterStateAutomata.State,
        stateBefore: TaintRegisterStateAutomata.State,
        position: PositionBaseWithModifiers?
    ): List<Clean> {
        compositionStrategy?.stateClean(state, stateBefore, varName, position)?.let { return it }

        if (varName == null || position == null) return emptyList()

        val markName = stateMarkName(varName, stateBefore)
            ?: return emptyList()

        return listOf(taintRuleStrategy.createCleanAction(markName, position))
    }

    fun containsStateMark(
        varName: MetavarAtom,
        state: TaintRegisterStateAutomata.State,
        position: PositionBaseWithModifiers
    ): Cond {
        compositionStrategy?.stateContains(state, varName, position)?.let { return it }

        val markName = stateMarkName(varName, state)
            ?: return taintRuleStrategy.conditionBuilder.mkFalse()

        return taintRuleStrategy.posContainsAnyMark(position, setOf(markName))
    }

    private fun usedTaintMarks(state: TaintRegisterStateAutomata.State): Set<Mark.GeneratedMark> =
        state.register.assignedVars.keys.flatMapTo(hashSetOf()) { mv ->
            compositionStrategy?.stateAccessedMarks(state, mv)?.let { return@flatMapTo it }
            setOfNotNull(stateMarkName(mv, state))
        }

    fun edgeRuleInfo(edge: TaintRuleEdge): UserRuleFromSemgrepInfo {
        val relevantTaintMarks = hashSetOf<Mark.GeneratedMark>()
        relevantTaintMarks += usedTaintMarks(edge.stateFrom)
        relevantTaintMarks += usedTaintMarks(edge.stateTo)
        if (edge.checkGlobalState || edge.stateTo in globalStateAssignStates) {
            relevantTaintMarks += globalStateMarkName(edge.stateTo)
        }

        val taintMarkNames = relevantTaintMarks.mapTo(hashSetOf()) { it.taintMarkStr() }
        return UserRuleFromSemgrepInfo(prefix.ruleId, taintMarkNames)
    }

    private fun allStates(): List<TaintRegisterStateAutomata.State> {
        val result = hashSetOf<TaintRegisterStateAutomata.State>()
        edges.flatMapTo(result) { listOf(it.stateFrom, it.stateTo) }
        edgesToFinalAccept.flatMapTo(result) { listOf(it.stateFrom, it.stateTo) }
        edgesToFinalDead.flatMapTo(result) { listOf(it.stateFrom, it.stateTo) }
        return result.toList()
    }

    private val allStates by lazy { allStates() }
    private val stateIndex by lazy { allStates.mapIndexed { i, s -> s to i }.toMap() }

    private fun statePredecessors(): List<BitSet> {
        val predecessors = List(allStates.size) { BitSet() }
        (edges + edgesToFinalAccept + edgesToFinalDead).forEach {
            val toIdx = stateIndex.getValue(it.stateTo)
            val fromIdx = stateIndex.getValue(it.stateFrom)
            predecessors[toIdx].set(fromIdx)
        }
        return predecessors
    }

    private fun stateTransitivePredecessors(): List<BitSet> {
        val predecessors = statePredecessors()

        do {
            var hasChanges = false
            for (states in predecessors) {
                val initialSize = states.cardinality()
                val allPredecessors = BitSet()
                states.forEach { allPredecessors.or(predecessors[it]) }
                states.or(allPredecessors)
                hasChanges = hasChanges || initialSize != states.cardinality()
            }
        } while (hasChanges)

        predecessors.forEachIndexed { index, set ->
            set.set(index)
        }

        return predecessors
    }

    private fun metaVarStates(): List<Map<MetavarAtom, BitSet>> {
        val transitivePredecessors = stateTransitivePredecessors()
        return transitivePredecessors.map { states ->
            val result = hashMapOf<MetavarAtom, BitSet>()
            states.forEach { stateId ->
                val state = allStates[stateId]
                state.register.assignedVars.keys.forEach { mv ->
                    result.getOrPut(mv, ::BitSet).set(stateId)
                }
            }
            result
        }
    }

    private val metaVarStates by lazy { metaVarStates() }

    private fun metaVarRelevantStates(state: TaintRegisterStateAutomata.State, varName: MetavarAtom): List<TaintRegisterStateAutomata.State> {
        val relevantMetaVarStates = metaVarStates[stateIndex.getValue(state)]
        val varStatesIndices = relevantMetaVarStates[varName] ?: error("MetaVar is not assigned")
        val varStates = mutableListOf<TaintRegisterStateAutomata.State>()
        varStatesIndices.forEach { varStates += allStates[it] }
        return varStates
    }

    fun containsMarkWithAnyStateBefore(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom,
        position: PositionBaseWithModifiers
    ): Cond {
        val varStates = metaVarRelevantStates(state, varName)
        val conditions = varStates.map { containsStateMark(varName, it, position) }
        return taintRuleStrategy.conditionBuilder.or(conditions)
    }

    private fun stateMarkName(varName: MetavarAtom, state: TaintRegisterStateAutomata.State): Mark.GeneratedMark? =
        state.register.assignedVars[varName]?.let { stateMarkName(varName, it) }

    private fun stateMarkName(varName: MetavarAtom, varValue: Int): Mark.GeneratedMark =
        prefix.metaVarState(varName, varValue)
}
