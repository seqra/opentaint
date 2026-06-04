package org.opentaint.dataflow.configuration.go.serialized

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers

sealed interface GoSerializedAction

sealed interface GoSerializedAssignAction : GoSerializedAction {
    val kind: String

    fun rawPosition(): PositionBaseWithModifiers
    fun changePos(newPos: PositionBaseWithModifiers): GoSerializedAssignAction

    data class Direct(
        override val kind: String,
        val pos: PositionBaseWithModifiers,
    ) : GoSerializedAssignAction {
        override fun rawPosition(): PositionBaseWithModifiers = pos
        override fun changePos(newPos: PositionBaseWithModifiers) = copy(pos = newPos)
    }

    data class AnyAccessor(
        override val kind: String,
        val pos: PositionBaseWithModifiers,
    ) : GoSerializedAssignAction {
        override fun rawPosition(): PositionBaseWithModifiers = pos
        override fun changePos(newPos: PositionBaseWithModifiers) = copy(pos = newPos)
    }

    companion object {
        operator fun invoke(kind: String, pos: PositionBaseWithModifiers) = Direct(kind, pos)
    }
}

data class GoSerializedCleanAction(
    val taintKind: String? = null,
    val pos: PositionBaseWithModifiers,
) : GoSerializedAction

data class GoSerializedPassAction(
    val taintKind: String? = null,
    val from: PositionBaseWithModifiers,
    val to: PositionBaseWithModifiers,
) : GoSerializedAction
