package org.opentaint.semgrep.pattern.conversion

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCondition
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonRule
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintAssignAction
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintCleanAction
import org.opentaint.semgrep.pattern.Mark
import org.opentaint.semgrep.pattern.conversion.LanguageStrategy.SinkDiscardMode
import org.opentaint.semgrep.pattern.conversion.taint.MarkConditionBuilder
import org.opentaint.semgrep.pattern.conversion.taint.RuleConversionCtx
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleGenerationCtx

/** TODO: emit Python taint config rules from converted patterns. */
data object PythonTaintStrategy :
    TaintRuleStrategy<SerializedPythonRule, SerializedPythonCondition, SerializedPythonTaintAssignAction, SerializedPythonTaintCleanAction> {

    override fun generateTaintRules(
        ctx: TaintRuleGenerationCtx<SerializedPythonRule, *, *, *>,
        ruleCtx: RuleConversionCtx,
        sinkDiscardMode: SinkDiscardMode,
    ): List<SerializedPythonRule> = TODO("Python taint rule generation not implemented")

    data object PythonMarkConditionBuilder : MarkConditionBuilder<SerializedPythonCondition> {
        override fun checkTaintMark(mark: Mark.GeneratedMark, pos: PositionBaseWithModifiers): SerializedPythonCondition =
            TODO("not implemented")

        override fun negate(cond: SerializedPythonCondition): SerializedPythonCondition = TODO("not implemented")
        override fun and(args: List<SerializedPythonCondition>): SerializedPythonCondition = TODO("not implemented")
        override fun or(args: List<SerializedPythonCondition>): SerializedPythonCondition = TODO("not implemented")
        override fun mkTrue(): SerializedPythonCondition = TODO("not implemented")
        override fun mkFalse(): SerializedPythonCondition = TODO("not implemented")
    }

    override val conditionBuilder = PythonMarkConditionBuilder

    override fun posContainsAnyMark(
        pos: PositionBaseWithModifiers,
        marks: Set<Mark.GeneratedMark>,
    ): SerializedPythonCondition = TODO("not implemented")

    override fun createCleanAction(
        mark: Mark.GeneratedMark,
        pos: PositionBaseWithModifiers,
    ): SerializedPythonTaintCleanAction = TODO("not implemented")

    override fun createAssignMark(
        mark: Mark.GeneratedMark,
        pos: PositionBaseWithModifiers,
    ): SerializedPythonTaintAssignAction = TODO("not implemented")

    override fun assignedMark(assign: SerializedPythonTaintAssignAction): Mark.GeneratedMark = TODO("not implemented")
}
