package org.opentaint.semgrep.pattern.conversion

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.semgrep.pattern.Mark
import org.opentaint.semgrep.pattern.conversion.LanguageStrategy.SinkDiscardMode
import org.opentaint.semgrep.pattern.conversion.taint.MarkConditionBuilder
import org.opentaint.semgrep.pattern.conversion.taint.RuleConversionCtx
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleGenerationCtx
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleGenerationCtx.CompositionStrategy

interface TaintRuleStrategy<R, Cond, Assign, Clean> {
    fun generateTaintRules(
        ctx: TaintRuleGenerationCtx<R, *, *, *>,
        ruleCtx: RuleConversionCtx,
        sinkDiscardMode: SinkDiscardMode
    ): List<R>

    val conditionBuilder: MarkConditionBuilder<Cond>

    fun posContainsAnyMark(pos: PositionBaseWithModifiers, marks: Set<Mark.GeneratedMark>): Cond
    fun createCleanAction(mark: Mark.GeneratedMark, pos: PositionBaseWithModifiers): Clean
    fun createAssignMark(mark: Mark.GeneratedMark, pos: PositionBaseWithModifiers): Assign
    fun assignedMark(assign: Assign): Mark.GeneratedMark
}
