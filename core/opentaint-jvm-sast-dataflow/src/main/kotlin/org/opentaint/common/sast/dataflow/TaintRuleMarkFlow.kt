package org.opentaint.common.sast.dataflow

import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.Condition
import org.opentaint.dataflow.configuration.jvm.ContainsMark
import org.opentaint.dataflow.configuration.jvm.CopyAllMarks
import org.opentaint.dataflow.configuration.jvm.CopyMark
import org.opentaint.dataflow.configuration.jvm.RemoveAllMarks
import org.opentaint.dataflow.configuration.jvm.RemoveMark
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough

internal data class TaintRuleMarkFlow(
    val inputMarks: Set<String>,
    val outputMarks: Set<String>,
    val outputMarksComplete: Boolean,
)

internal fun CommonTaintConfigurationItem.taintRuleMarkFlow(
    actions: Set<CommonTaintAction>,
): TaintRuleMarkFlow {
    val condition = when (this) {
        is TaintConfigurationSource -> condition
        is TaintConfigurationSink -> condition
        is TaintPassThrough -> condition
        is TaintCleaner -> condition
        else -> null
    }
    val outputMarks = hashSetOf<String>()
    var outputMarksComplete = true
    actions.forEach { action ->
        when (action) {
            is AssignMark -> outputMarks += action.mark.name
            is CopyMark -> outputMarks += action.mark.name
            is RemoveMark, is RemoveAllMarks -> Unit
            is CopyAllMarks -> outputMarksComplete = false
            else -> outputMarksComplete = false
        }
    }
    return TaintRuleMarkFlow(
        inputMarks = condition?.taintMarks().orEmpty(),
        outputMarks = outputMarks,
        outputMarksComplete = outputMarksComplete,
    )
}

private fun Condition.taintMarks(): Set<String> = buildSet {
    fun collect(condition: CommonCondition<*>) {
        when (condition) {
            CommonCondition.True -> Unit
            is CommonCondition.Atom<*> -> {
                val atom = condition.atom
                if (atom is ContainsMark) add(atom.mark.name)
            }
            is CommonCondition.Not<*> -> collect(condition.arg)
            is CommonCondition.And<*> -> condition.args.forEach(::collect)
            is CommonCondition.Or<*> -> condition.args.forEach(::collect)
        }
    }
    collect(this@taintMarks)
}
