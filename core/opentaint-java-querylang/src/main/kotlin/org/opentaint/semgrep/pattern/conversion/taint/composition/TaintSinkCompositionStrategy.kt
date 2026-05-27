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

class TaintSinkCompositionStrategy<Item, Cond, Assign, Clean>(
    rule: TaintAutomataEdges,
    private val requires: TaintMarkCheckBuilder,
    private val strategy: TaintRuleStrategy<Item, Cond, Assign, Clean>
) : TaintRuleGenerationCtx.CompositionStrategy<Item, Cond, Assign, Clean> {
    private val initialStateId = rule.automata.stateId(rule.automata.initial)

    override fun stateContains(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom,
        pos: PositionBaseWithModifiers
    ): Cond? {
        val value = state.register.assignedVars[varName]
        if (value != initialStateId) return null
        return requires.build(strategy.conditionBuilder, pos)
    }

    override fun stateAccessedMarks(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom
    ): Set<Mark.GeneratedMark>? {
        val value = state.register.assignedVars[varName]
        if (value != initialStateId) return null
        return requires.collectLabels(hashSetOf())
    }
}
