package org.opentaint.semgrep.pattern.conversion.taint.composition

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.semgrep.pattern.Mark
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.TaintRuleStrategy
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataEdges
import org.opentaint.semgrep.pattern.conversion.taint.TaintMarkCheckBuilder
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleGenerationCtx.CompositionStrategy
import org.opentaint.semgrep.pattern.conversion.taint.collectLabels

class TaintPassCompositionStrategy<Item, Cond, Assign, Clean>(
    private val rule: TaintAutomataEdges,
    private val markRequires: TaintMarkCheckBuilder,
    private val markName: Mark.GeneratedMark,
    val strategy: TaintRuleStrategy<Item, Cond, Assign, Clean>
) : CompositionStrategy<Item, Cond, Assign, Clean> {
    private val initialStateId = rule.automata.stateId(rule.automata.initial)

    override fun stateContains(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom,
        pos: PositionBaseWithModifiers
    ): Cond? {
        val value = state.register.assignedVars[varName]
        if (value != initialStateId) return null
        return markRequires.build(strategy.conditionBuilder, pos)
    }

    override fun stateAssign(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom,
        pos: PositionBaseWithModifiers
    ): List<Assign>? {
        if (state !in rule.automata.finalAcceptStates) return null
        return listOf(strategy.createAssignMark(markName, pos))
    }

    override fun stateAccessedMarks(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom
    ): Set<Mark.GeneratedMark>? {
        val value = state.register.assignedVars[varName]
        if (value == initialStateId) {
            return markRequires.collectLabels(hashSetOf())
        }
        if (state in rule.automata.finalAcceptStates) {
            return setOf(markName)
        }
        return null
    }
}
