package org.opentaint.ir.go.value

import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.go.type.GoIRType

/**
 * Base interface for all IR values.
 * A value is anything that can be used as an operand of an instruction.
 */
interface GoIRValue: CommonValue {
    val type: GoIRType
    val name: String

    override val typeName: String get() = type.typeName

    fun <T> acceptValue(visitor: GoIRValueVisitor<T>): T
}

/**
 * An SSA register — a named, typed storage location that holds the result of a
 * value-defining instruction (GoIRAssignInst, GoIRPhi, GoIRCall).
 *
 * Other instructions reference registers, never instruction objects directly.
 * Each register is defined by exactly one instruction.
 */
data class GoIRRegister(
    override var type: GoIRType,
    val index: Int,
    override val name: String,
) : GoIRValue {
    override fun <T> acceptValue(visitor: GoIRValueVisitor<T>): T = visitor.visitRegister(this)
    override fun toString(): String = "%${index}:$name"
}

/** Sealed interface for constant value representations. */
sealed interface GoIRConstantValue {
    data class IntConst(val value: Long) : GoIRConstantValue
    data class FloatConst(val value: Double) : GoIRConstantValue
    data class ComplexConst(val real: Double, val imag: Double) : GoIRConstantValue
    data class StringConst(val value: String) : GoIRConstantValue
    data class BoolConst(val value: Boolean) : GoIRConstantValue
    data object NilConst : GoIRConstantValue
}

// ─── Non-instruction values ─────────────────────────────────────────

data class GoIRConstValue(
    override val type: GoIRType,
    override val name: String,
    val value: GoIRConstantValue,
) : GoIRValue {
    override fun <T> acceptValue(visitor: GoIRValueVisitor<T>): T = visitor.visitConst(this)
    override fun toString(): String = when (value) {
        is GoIRConstantValue.IntConst -> value.value.toString()
        is GoIRConstantValue.FloatConst -> value.value.toString()
        is GoIRConstantValue.ComplexConst -> "(${value.real}+${value.imag}i)"
        is GoIRConstantValue.StringConst -> "\"${value.value}\""
        is GoIRConstantValue.BoolConst -> value.value.toString()
        GoIRConstantValue.NilConst -> "nil"
    }
}

data class GoIRParameterValue(
    override val type: GoIRType,
    override val name: String,
    val paramIndex: Int,
) : GoIRValue {
    override fun <T> acceptValue(visitor: GoIRValueVisitor<T>): T = visitor.visitParameter(this)
    override fun toString(): String = "arg${paramIndex}:$name"
}
