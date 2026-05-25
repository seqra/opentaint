package org.opentaint.dataflow.go.rules.serialized

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers

sealed interface GoSerializedAction

data class GoSerializedAssignAction(
    val kind: String,
    val pos: PositionBaseWithModifiers,
) : GoSerializedAction

data class GoSerializedCleanAction(
    val taintKind: String? = null,
    val pos: PositionBaseWithModifiers,
) : GoSerializedAction

data class GoSerializedPassAction(
    val taintKind: String? = null,
    val from: PositionBaseWithModifiers,
    val to: PositionBaseWithModifiers,
) : GoSerializedAction
