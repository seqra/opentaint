package org.opentaint.ir.api.python

/**
 * A value used as an operand or result of a PIR instruction.
 *
 * `PIRValue` is exactly `PIRLocal | PIRConst` — a function-local slot
 * (variable, temporary, or parameter) or a literal constant. Name
 * resolution (global / module references) is **not** a value: it is an
 * explicit [PIRReadName] instruction whose result lands in a local.
 *
 * Values are also expressions ([PIRExpr]) since they can appear as the
 * right-hand side of [PIRAssign].
 */
sealed interface PIRValue : PIRExpr, org.opentaint.ir.api.common.cfg.CommonValue {
    val type: PIRType
    override val typeName: String get() = type.typeName
    fun <T> accept(visitor: PIRValueVisitor<T>): T
}

// ─── Locals & Parameters ────────────────────────────────────

/**
 * Common supertype for any reference to a function-local slot:
 * either a body-local variable / temporary ([PIRLocalVar]) or a
 * parameter reference ([PIRParameterRef]).
 *
 * Each instance carries an [index] that uniquely identifies the slot
 * within its enclosing function. Parameter indices match
 * [PIRParameter.index] (signature order, starting at 0); local indices
 * start at `parameters.size` so the param + local index space is
 * disjoint within one function.
 *
 * Equality on the concrete subclasses ([PIRLocalVar], [PIRParameterRef])
 * is keyed on `(javaClass, index)`. This is meaningful only *within* one
 * function — two values from different functions that happen to share an
 * index will compare equal. Do not use [PIRLocal] instances as keys in
 * maps or sets that span multiple functions.
 */
sealed interface PIRLocal : PIRValue {
    val name: String
    val index: Int
}

/** A local variable or temporary (e.g., "$t0", "result"). */
class PIRLocalVar(
    override val name: String,
    override val type: PIRType,
    override val index: Int,
) : PIRLocal {
    override fun toString(): String = "%$index:$name"
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitLocalVar(this)

    override fun equals(other: Any?): Boolean =
        this === other || (other is PIRLocalVar && other.index == index)
    override fun hashCode(): Int = index
}

/**
 * Reference to a function parameter, identified by [name] and its
 * signature-order [index].
 *
 * Emitted by the parameter-binding prologue at function entry — one
 * `PIRAssign(PIRLocalVar(name), PIRParameterRef(name))` per parameter —
 * and by the closure rewriter's prologue when reading the synthetic
 * `<self>` env parameter on capturing children. The closure rewriter
 * prepends a `<self>` parameter to capturing children; the [index] here
 * is the *post-rewrite* signature index, populated by the Flat → PIR
 * converter from the (already-rewritten) [PIRFunction.parameters].
 */
class PIRParameterRef(
    override val name: String,
    override val type: PIRType,
    override val index: Int,
) : PIRLocal {
    override fun toString(): String = name
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitParameterRef(this)

    override fun equals(other: Any?): Boolean =
        this === other || (other is PIRParameterRef && other.index == index)
    override fun hashCode(): Int = index
}

// ─── Constants ──────────────────────────────────────────────

sealed interface PIRConst : PIRValue

data class PIRIntConst(val value: Long) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.int")
    override fun toString(): String = value.toString()
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitIntConst(this)
}

data class PIRFloatConst(val value: Double) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.float")
    override fun toString(): String = value.toString()
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitFloatConst(this)
}

data class PIRStrConst(val value: String) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.str")
    override fun toString(): String = "\"$value\""
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitStrConst(this)
}

data class PIRBoolConst(val value: Boolean) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.bool")
    override fun toString(): String = if (value) "True" else "False"
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitBoolConst(this)
}

data object PIRNoneConst : PIRConst {
    override val type: PIRType = PIRNoneType
    override fun toString(): String = "None"
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitNoneConst(this)
}

data object PIREllipsisConst : PIRConst {
    override val type: PIRType = PIRAnyType
    override fun toString(): String = "..."
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitEllipsisConst(this)
}

data class PIRBytesConst(val value: ByteArray) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.bytes")
    override fun equals(other: Any?): Boolean =
        other is PIRBytesConst && value.contentEquals(other.value)
    override fun hashCode(): Int = value.contentHashCode()
    override fun toString(): String = "b\"...\""
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitBytesConst(this)
}

data class PIRComplexConst(val real: Double, val imag: Double) : PIRConst {
    override val type: PIRType get() = PIRClassType("builtins.complex")
    override fun toString(): String = "${real}+${imag}j"
    override fun <T> accept(visitor: PIRValueVisitor<T>): T = visitor.visitComplexConst(this)
}

// ─── Name references (NOT values) ───────────────────────────

/**
 * A structural name that the IR must resolve to a value at runtime.
 * Carried by [PIRReadName] (read), [PIRStoreGlobal] / [PIRDeleteGlobal]
 * (write/delete of a global), and [PIRBindFunctionExpr] (structural
 * reference to a lifted function).
 *
 * Name refs are deliberately not [PIRValue]: resolution is a
 * side-effecting load, distinct from an operand read. Spilling a name
 * into a local via `PIRReadName(tmp, ref)` makes the resolution an
 * explicit instruction in the CFG.
 */
sealed interface PIRNameRef

/**
 * A reference to a global variable or imported name, identified by its
 * canonical qualified name (e.g. `os.getcwd`, `builtins.super`,
 * `mypkg.module.func`).
 */
data class PIRGlobalNameRef(val qualifiedName: String) : PIRNameRef {
    override fun toString(): String = qualifiedName
}

/**
 * A reference to a module by its top-level segment (e.g. `os` in
 * `os.getcwd()`). Sub-module access (e.g. `os.path`) is uniformly
 * represented as a [PIRLoadAttr] chain rooted at a local that was
 * filled by `PIRReadName(tmp, PIRModuleNameRef("os"))`.
 *
 * `module` must be a single segment with no dots.
 */
data class PIRModuleNameRef(val module: String) : PIRNameRef {
    init {
        require('.' !in module) { "PIRModuleNameRef.module must be a single segment, got '$module'" }
    }
    override fun toString(): String = module
}
