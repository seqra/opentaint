package org.opentaint.semgrep.pattern.conversion.taint.composition

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.semgrep.pattern.Mark
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.TaintRuleStrategy
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataEdges
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleGenerationCtx

class JoinRightCompositionStrategy<Item, Cond, Assign, Clean>(
    r: TaintAutomataEdges,
    private val initialVar: MetavarAtom,
    private val leftFinalMarks: Set<Mark.GeneratedMark>,
    val strategy: TaintRuleStrategy<Item, Cond, Assign, Clean>,
) : TaintRuleGenerationCtx.CompositionStrategy<Item, Cond, Assign, Clean> {
    private var joinVarUsed: Boolean = false
    val joinVarReferenced: Boolean get() = joinVarUsed

    private val initialStateId = r.automata.stateId(r.automata.initial)

    override fun stateContains(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom, pos: PositionBaseWithModifiers
    ): Cond? {
        if (varName != initialVar) return null
        val value = state.register.assignedVars[varName]
        if (value != initialStateId) return null

        joinVarUsed = true
        return strategy.posContainsAnyMark(pos, leftFinalMarks)
    }

    override fun stateContainsOnAnyField(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom,
        pos: PositionBaseWithModifiers
    ): Cond? {
        if (varName != initialVar) return null
        val value = state.register.assignedVars[varName]
        if (value != initialStateId) return null

        val builder = strategy.conditionBuilder
        return builder.or(leftFinalMarks.map { builder.checkTaintMarkOnAnyField(it, pos) })
    }

    override fun stateAccessedMarks(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom
    ): Set<Mark.GeneratedMark>? {
        if (varName != initialVar) return null
        val value = state.register.assignedVars[varName]
        if (value != initialStateId) return null
        return leftFinalMarks
    }
}
