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

data class GoAssignMark(val mark: String, val pos: Position): GoTaintAction, CommonTaintAssignAction
