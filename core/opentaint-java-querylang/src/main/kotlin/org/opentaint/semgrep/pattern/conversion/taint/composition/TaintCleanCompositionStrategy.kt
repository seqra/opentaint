package org.opentaint.semgrep.pattern.conversion.taint.composition

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.semgrep.pattern.Mark
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.TaintRuleStrategy
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataEdges
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleGenerationCtx
import org.opentaint.semgrep.pattern.conversion.taint.base

class TaintCleanCompositionStrategy<Item, Cond, Assign, Clean>(
    private val rule: TaintAutomataEdges,
    private val bySideEffect: Boolean,
    private val cleans: Set<Mark.GeneratedMark>,
    val strategy: TaintRuleStrategy<Item, Cond, Assign, Clean>
) : TaintRuleGenerationCtx.CompositionStrategy<Item, Cond, Assign, Clean> {
    override fun stateClean(
        state: TaintRegisterStateAutomata.State,
        stateBefore: TaintRegisterStateAutomata.State,
        varName: MetavarAtom?,
        pos: PositionBaseWithModifiers?
    ): List<Clean>? {
        if (state !in rule.automata.finalAcceptStates) return null

        val cleanerPos = mutableListOf(PositionBase.Result.base())
        if (bySideEffect) {
            cleanerPos += PositionBase.AnyArgument(classifier = "tainted").base()
            cleanerPos += PositionBase.This.base()
        }

        return cleans.flatMap { c -> cleanerPos.map { strategy.createCleanAction(c, it) } }
    }

    override fun stateAccessedMarks(
        state: TaintRegisterStateAutomata.State,
        varName: MetavarAtom
    ): Set<Mark.GeneratedMark>? {
        if (state !in rule.automata.finalAcceptStates) return null
        return cleans
    }
}
