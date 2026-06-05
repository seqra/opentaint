package org.opentaint.semgrep.pattern.conversion.taint.composition

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.semgrep.pattern.Mark
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.TaintRuleStrategy
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataEdges
import org.opentaint.semgrep.pattern.conversion.taint.TaintMarkCheckBuilder
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleGenerationCtx
import org.opentaint.semgrep.pattern.conversion.taint.collectLabels

class TaintSourceCompositionStrategy<Item, Cond, Assign, Clean>(
    private val rule: TaintAutomataEdges,
    private val requires: TaintMarkCheckBuilder?,
    private val taintedVars: Set<MetavarAtom>,
    private val label: Mark.GeneratedMark,
    val strategy: TaintRuleStrategy<Item, Cond, Assign, Clean>
) : TaintRuleGenerationCtx.CompositionStrategy<Item, Cond, Assign, Clean> {
    private val initialStateId = rule.automata.stateId(rule.automata.initial)

    override fun stateContains(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom,
        pos: PositionBaseWithModifiers
    ): Cond? {
        if (requires == null) return null

        val value = state.register.assignedVars[varName]
        if (value != initialStateId) return null

        return requires.build(strategy.conditionBuilder, pos)
    }

    override fun stateAssign(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom,
        pos: PositionBaseWithModifiers
    ): List<Assign>? {
        if (state !in rule.automata.finalAcceptStates) return null
        if (varName !in taintedVars) return null
        return listOf(strategy.createAssignTaintMark(label, pos))
    }

    override fun stateAccessedMarks(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom
    ): Set<Mark.GeneratedMark>? {
        if (requires == null) return null

        val value = state.register.assignedVars[varName]
        if (value == initialStateId) {
            return requires.collectLabels(hashSetOf())
        }

        if (state in rule.automata.finalAcceptStates) {
            if (varName in taintedVars) {
                return setOf(label)
            }
        }

        return null
    }
}
