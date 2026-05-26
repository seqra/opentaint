package org.opentaint.ir.go.inst

import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.go.api.GoIRBody
import org.opentaint.ir.go.api.GoIRPosition
import org.opentaint.ir.go.cfg.GoIRBasicBlock
import org.opentaint.ir.go.cfg.GoIRCallInfo
import org.opentaint.ir.go.expr.GoIRExpr
import org.opentaint.ir.go.value.GoIRRegister
import org.opentaint.ir.go.value.GoIRValue

data class GoInstLocation(
    val functionBody: GoIRBody,
    val index: Int,
    val blockIndex: Int,
    val position: GoIRPosition?
) : CommonInstLocation {
    override val method: CommonMethod get() = functionBody.function
}

/**
 * Base interface for all IR instructions.
 * Every instruction belongs to a basic block and has a unique index within its function.
 */
sealed interface GoIRInst: CommonInst {
    override val location: GoInstLocation
    val operands: List<GoIRValue>

    fun <T> accept(visitor: GoIRInstVisitor<T>): T
}

val GoIRInst.index: Int get() = location.index

val GoIRInst.block: GoIRBasicBlock get() = location.functionBody.blocks[location.blockIndex]

val GoIRInst.position: GoIRPosition? get() = location.position

/**
 * A value-defining instruction: an instruction that writes its result into a [GoIRRegister].
 * Subtyped by [GoIRAssignInst], [GoIRPhi], and [GoIRCall].
 *
 * Other instructions reference the [register], never the instruction itself.
 */
sealed interface GoIRDefInst : GoIRInst {
    val register: GoIRRegister
}

/** Marker for terminator instructions (last in block). */
sealed interface GoIRTerminator : GoIRInst

/** Marker for branching terminators (Jump, If). */
sealed interface GoIRBranching : GoIRTerminator {
    val successors: List<GoIRInstRef>
}

// ─── Value-defining instructions ────────────────────────────────────

/**
 * Assignment instruction: `register = expr`.
 * Wraps a [GoIRExpr] that computes the value stored into [register].
 * This covers 24 expression kinds (alloc, binop, unop, conversions, field access, etc.).
 */
data class GoIRAssignInst(
    override val location: GoInstLocation,
    override val register: GoIRRegister,
    val expr: GoIRExpr,
) : GoIRDefInst {
    override val operands: List<GoIRValue> get() = expr.operands
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitAssign(this)
    override fun toString(): String = "$register = $expr"
}

/**
 * Phi instruction: merges values from predecessor blocks at a join point.
 * Each edge is keyed by the predecessor block terminator instruction reference.
 */
data class GoIRPhi(
    override val location: GoInstLocation,
    override val register: GoIRRegister,
    val edges: Map<GoIRInstRef, GoIRValue>,
    val comment: String?,
) : GoIRDefInst {
    override val operands: List<GoIRValue> get() = edges.entries.sortedBy { it.key.index }.map { it.value }
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitPhi(this)
    override fun toString(): String {
        val args = edges.entries.sortedBy { it.key.index }
            .joinToString(", ") { (ref, value) -> "${ref.index}: $value" }
        val suffix = comment?.let { "  // $it" } ?: ""
        return "$register = phi($args)$suffix"
    }
}

/**
 * Call instruction: invokes a function and stores the result into [register].
 */
data class GoIRCall(
    override val location: GoInstLocation,
    override val register: GoIRRegister,
    val call: GoIRCallInfo,
) : GoIRDefInst {
    override val operands: List<GoIRValue> get() = call.allOperands()
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitCall(this)
    override fun toString(): String = "$register = ${call.render()}"
}

// ─── Terminators ────────────────────────────────────────────────────

data class GoIRJump(
    override val location: GoInstLocation,
    val target: GoIRInstRef,
) : GoIRBranching {
    override val operands: List<GoIRValue> get() = emptyList()
    override val successors: List<GoIRInstRef> get() = listOf(target)
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitJump(this)
    override fun toString(): String = "jump $target"
}

data class GoIRIf(
    override val location: GoInstLocation,
    val cond: GoIRValue,
    val trueBranch: GoIRInstRef,
    val falseBranch: GoIRInstRef,
) : GoIRBranching {
    override val operands: List<GoIRValue> get() = listOf(cond)
    override val successors: List<GoIRInstRef> get() = listOf(trueBranch, falseBranch)
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitIf(this)
    override fun toString(): String = "if ($cond) then $trueBranch else $falseBranch"
}

data class GoIRReturn(
    override val location: GoInstLocation,
    val results: List<GoIRValue>,
) : GoIRTerminator {
    override val operands: List<GoIRValue> get() = results
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitReturn(this)
    override fun toString(): String =
        if (results.isEmpty()) "return" else "return ${results.joinToString(", ")}"
}

data class GoIRPanic(
    override val location: GoInstLocation,
    val x: GoIRValue,
) : GoIRTerminator {
    override val operands: List<GoIRValue> get() = listOf(x)
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitPanic(this)
    override fun toString(): String = "panic $x"
}

// ─── Effect-only instructions ───────────────────────────────────────

data class GoIRStore(
    override val location: GoInstLocation,
    val addr: GoIRValue,
    val value: GoIRValue,
) : GoIRInst {
    override val operands: List<GoIRValue> get() = listOf(addr, value)
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitStore(this)
    override fun toString(): String = "*$addr = $value"
}

data class GoIRMapUpdate(
    override val location: GoInstLocation,
    val map: GoIRValue,
    val key: GoIRValue,
    val value: GoIRValue,
) : GoIRInst {
    override val operands: List<GoIRValue> get() = listOf(map, key, value)
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitMapUpdate(this)
    override fun toString(): String = "$map[$key] = $value"
}

data class GoIRSend(
    override val location: GoInstLocation,
    val chan: GoIRValue,
    val x: GoIRValue,
) : GoIRInst {
    override val operands: List<GoIRValue> get() = listOf(chan, x)
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitSend(this)
    override fun toString(): String = "send $chan <- $x"
}

data class GoIRGo(
    override val location: GoInstLocation,
    val call: GoIRCallInfo,
) : GoIRInst {
    override val operands: List<GoIRValue> get() = call.allOperands()
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitGo(this)
    override fun toString(): String = "go ${call.render()}"
}

data class GoIRDefer(
    override val location: GoInstLocation,
    val call: GoIRCallInfo,
) : GoIRInst {
    override val operands: List<GoIRValue> get() = call.allOperands()
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitDefer(this)
    override fun toString(): String = "defer ${call.render()}"
}

data class GoIRRunDefers(
    override val location: GoInstLocation,
) : GoIRInst {
    override val operands: List<GoIRValue> get() = emptyList()
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitRunDefers(this)
    override fun toString(): String = "rundefers"
}

data class GoIRDebugRef(
    override val location: GoInstLocation,
    val x: GoIRValue,
    val isAddr: Boolean,
) : GoIRInst {
    override val operands: List<GoIRValue> get() = listOf(x)
    override fun <T> accept(visitor: GoIRInstVisitor<T>): T = visitor.visitDebugRef(this)
    override fun toString(): String = "debugref ${if (isAddr) "&" else ""}$x"
}

private fun GoIRCallInfo.render(): String {
    val argsStr = args.joinToString(", ")
    return when {
        receiver != null && methodName != null -> "$receiver.$methodName($argsStr)"
        function != null -> "$function($argsStr)"
        else -> "call($argsStr)"
    }
}
