package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase

sealed interface GoRuleCondition {
    data class ContainsMark(val position: PositionBase, val mark: String) : GoRuleCondition
}
