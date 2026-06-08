package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintAssignAction

sealed interface GoTaintAction : CommonTaintAction

data class CopyTaintMark(
    val mark: String,
    val from: Position,
    val to: Position,
) : GoTaintAction

data class CopyData(
    val from: Position,
    val to: Position,
) : GoTaintAction

data class RemoveMark(
    val mark: String,
    val pos: Position,
) : GoTaintAction

data class RemoveAllMarks(
    val pos: Position,
) : GoTaintAction

sealed interface GoAssignAction : GoTaintAction, CommonTaintAssignAction {
    val mark: String
    fun rawPosition(): Position

    data class Direct(override val mark: String, val pos: Position) : GoAssignAction {
        override fun rawPosition(): Position = pos
    }

    data class AnyAccessor(override val mark: String, val pos: Position) : GoAssignAction {
        override fun rawPosition(): Position = pos
    }
}
