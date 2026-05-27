package org.opentaint.semgrep.pattern.conversion

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedItem
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintCleanAction
import org.opentaint.dataflow.configuration.jvm.serialized.SinkRule
import org.opentaint.semgrep.pattern.Mark
import org.opentaint.semgrep.pattern.TaintRuleMatchAnything
import org.opentaint.semgrep.pattern.conversion.LanguageStrategy.SinkDiscardMode
import org.opentaint.semgrep.pattern.conversion.taint.JavaMarkConditionBuilder
import org.opentaint.semgrep.pattern.conversion.taint.RuleConversionCtx
import org.opentaint.semgrep.pattern.conversion.taint.TaintRuleGenerationCtx
import org.opentaint.semgrep.pattern.conversion.taint.emitJavaTaintRules
import org.opentaint.semgrep.pattern.conversion.taint.matchAnything
import org.opentaint.semgrep.pattern.conversion.taint.mkAssignMark
import org.opentaint.semgrep.pattern.conversion.taint.mkCleanMark
import org.opentaint.semgrep.pattern.conversion.taint.mkContainsMark
import org.opentaint.semgrep.pattern.conversion.taint.serializedConditionOr

typealias JavaTaintRuleGenerationCtx = TaintRuleGenerationCtx<SerializedItem, SerializedCondition, SerializedTaintAssignAction, SerializedTaintCleanAction>

data object JavaTaintRuleStrategy :
    TaintRuleStrategy<SerializedItem, SerializedCondition, SerializedTaintAssignAction, SerializedTaintCleanAction> {
    override fun generateTaintRules(
        ctx: TaintRuleGenerationCtx<SerializedItem, *, *, *>,
        ruleCtx: RuleConversionCtx,
        sinkDiscardMode: SinkDiscardMode
    ): List<SerializedItem> {
        val javaCtx = ctx.javaCtx()
        val rules = javaCtx.emitJavaTaintRules(ruleCtx)
        if (sinkDiscardMode == SinkDiscardMode.NONE) return rules

        return rules.filter { r ->
            if (r !is SinkRule) return@filter true
            if (r.condition != null && r.condition !is SerializedCondition.True) return@filter true

            if (sinkDiscardMode == SinkDiscardMode.TRIVIAL_CONDITION_WITH_EMPTY_FUNCTION) {
                val function = when (r) {
                    is SerializedRule.MethodEntrySink -> r.function
                    is SerializedRule.MethodExitSink -> r.function
                    is SerializedRule.Sink -> r.function
                }

                if (!function.matchAnything()) return@filter true
            }

            ruleCtx.trace.error(TaintRuleMatchAnything())
            false
        }
    }

    override val conditionBuilder get() = JavaMarkConditionBuilder

    override fun posContainsAnyMark(
        pos: PositionBaseWithModifiers,
        marks: Set<Mark.GeneratedMark>
    ): SerializedCondition =
        serializedConditionOr(
            marks.map {
                it.mkContainsMark(pos)
            }
        )

    override fun createCleanAction(
        mark: Mark.GeneratedMark,
        pos: PositionBaseWithModifiers
    ): SerializedTaintCleanAction = mark.mkCleanMark(pos)

    override fun createAssignMark(
        mark: Mark.GeneratedMark,
        pos: PositionBaseWithModifiers
    ): SerializedTaintAssignAction = mark.mkAssignMark(pos)

    override fun assignedMark(assign: SerializedTaintAssignAction): Mark.GeneratedMark =
        Mark.parseMark(assign.kind)

    @Suppress("UNCHECKED_CAST")
    private fun TaintRuleGenerationCtx<SerializedItem, *, *, *>.javaCtx(): JavaTaintRuleGenerationCtx =
        this as JavaTaintRuleGenerationCtx
}
