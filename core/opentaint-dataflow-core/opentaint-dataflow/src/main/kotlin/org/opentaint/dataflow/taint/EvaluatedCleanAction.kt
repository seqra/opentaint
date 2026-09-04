package org.opentaint.dataflow.taint

import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem

data class EvaluatedCleanAction(
    val fact: FinalFactReader?,
    val action: ActionInfo?,
) {
    data class ActionInfo(
        val rule: CommonTaintConfigurationItem,
        val action: CommonTaintAction,
    )

    companion object {
        fun initial(fact: FinalFactReader) = EvaluatedCleanAction(
            action = null, fact = fact
        )
    }
}
