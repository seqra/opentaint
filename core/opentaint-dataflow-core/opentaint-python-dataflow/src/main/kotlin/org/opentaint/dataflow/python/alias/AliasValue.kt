package org.opentaint.dataflow.python.alias

import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.ir.api.python.PIRLocalVar
import org.opentaint.ir.api.python.PIRParameterRef
import org.opentaint.ir.api.python.PIRValue

/**
 * Context-tagged alias value — the only PIR-independent value layer the alias DSU
 * needs (the simulator otherwise dispatches directly on PIR instructions).
 *
 * PIR locals/params are equal by index only, so a callee local inlined in a child
 * context would collide with the caller's local of the same index. [RefValue.Local]
 * tags the index with its frame [ContextInfo] to keep frames distinct.
 */
sealed interface RefValue : Comparable<RefValue> {
    val valueKind: Int

    override fun compareTo(other: RefValue): Int {
        val kindCmp = valueKind.compareTo(other.valueKind)
        if (kindCmp != 0) return kindCmp
        return compareValue(other)
    }

    fun compareValue(other: RefValue): Int

    data class Local(val idx: Int, val ctx: ContextInfo) : RefValue {
        override val valueKind: Int get() = 0

        override fun compareValue(other: RefValue): Int {
            other as Local
            val idxCmp = idx.compareTo(other.idx)
            if (idxCmp != 0) return idxCmp
            return ctx.compareTo(other.ctx)
        }
    }

    data class Arg(val idx: Int) : RefValue {
        override val valueKind: Int get() = 1

        override fun compareValue(other: RefValue): Int = idx.compareTo((other as Arg).idx)
    }
}

/**
 * Maps PIR values to context-tagged [RefValue]s. The root frame maps locals/params
 * identically (tagging with the root context); inlined callee frames substitute
 * parameters with the caller-frame actuals (see [NestedCallInstEvalCtx]).
 */
interface InstEvalContext {
    fun createArg(idx: Int): RefValue
    fun createLocal(idx: Int): RefValue.Local
}

/** Converts a PIR value to a context-tagged [RefValue], or null if not ref-trackable (constant). */
fun InstEvalContext.refValue(value: PIRValue): RefValue? = when (value) {
    is PIRLocalVar -> createLocal(value.index)
    is PIRParameterRef -> createArg(value.index)
    else -> null
}
