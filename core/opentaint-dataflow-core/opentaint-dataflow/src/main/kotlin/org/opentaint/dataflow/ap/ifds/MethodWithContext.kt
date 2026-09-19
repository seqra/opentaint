package org.opentaint.dataflow.ap.ifds

import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst

interface MethodContext

data object EmptyMethodContext : MethodContext {
    override fun toString(): String = "{}"
}

data class CombinedMethodContext(val first: MethodContext, val second: MethodContext) : MethodContext {
    override fun toString() = "$first & $second"
}

fun Set<MethodContext>.combine(): MethodContext = reduce { acc, context ->
    if (context is EmptyMethodContext) return@reduce acc
    if (acc is EmptyMethodContext) return@reduce context
    CombinedMethodContext(acc, context)
}

data class MethodWithContext(val method: CommonMethod, val ctx: MethodContext)

/**
 * A hash-map key almost everywhere: the per-unit summary storage, the subscription maps, the
 * analyzer registry and every side-effect kind that carries an entry point. `statement.hashCode()`
 * chases `JIRInst -> JIRInstLocation -> JIRMethod -> JIRClassOrInterface`, so the data-class hash
 * was five virtual calls deep on every lookup. The fields are immutable; the hash is the same
 * value, computed once.
 */
class MethodEntryPoint(val context: MethodContext, val statement: CommonInst) {
    val method: CommonMethod get() = statement.location.method

    private val hash: Int = 31 * context.hashCode() + statement.hashCode()

    operator fun component1(): MethodContext = context
    operator fun component2(): CommonInst = statement

    fun copy(context: MethodContext = this.context, statement: CommonInst = this.statement): MethodEntryPoint =
        MethodEntryPoint(context, statement)

    override fun hashCode(): Int = hash

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is MethodEntryPoint) return false

        if (hash != other.hash) return false
        if (statement != other.statement) return false
        return context == other.context
    }

    override fun toString(): String = "$method [$context]"
}
