package org.opentaint.dataflow.go.rules

sealed interface Position {
    sealed interface Simple : Position

    data class Argument(val index: Int) : Simple

    data object This : Simple {
        override fun toString(): String = javaClass.simpleName
    }

    data object Result : Simple {
        override fun toString(): String = javaClass.simpleName
    }

    // A named global slot (the querylang state-var mechanism); mirrors the JVM
    // Position.ClassStatic and resolves to the ClassStatic access-path base with a
    // ClassStaticAccessor carrying the name.
    data class ClassStatic(val className: String) : Simple
}

sealed interface PositionAccessor {
    data object ElementAccessor : PositionAccessor {
        override fun toString(): String = javaClass.simpleName
    }

    data class FieldAccessor(
        val className: String,
        val fieldName: String,
        val fieldType: String
    ) : PositionAccessor

    data object AnyAccessor : PositionAccessor
}

data class PositionWithAccess(
    val base: Position,
    val access: PositionAccessor
) : Position
