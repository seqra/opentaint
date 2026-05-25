package org.opentaint.dataflow.go.rules

sealed interface GoTaintAction

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
