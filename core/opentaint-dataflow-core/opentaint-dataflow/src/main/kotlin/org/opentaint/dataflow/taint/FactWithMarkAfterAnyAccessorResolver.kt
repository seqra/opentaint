package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.util.UnfoldClimbBound

interface FactWithMarkAfterAnyAccessorResolver {
    fun resolve(mark: TaintMarkAccessor)
}

/**
 * `suffix` is an arbitrary access-tree delta belonging to whichever caller happened to refine the
 * request. Including it in the identity turns the per-method side-effect map -- whose natural key is
 * the diagonal (method, fact, mark) -- into a product with a *global* dimension, so the same request
 * is stored and re-broadcast once per distinct caller shape. On tms that is 311,443 distinct keys for
 * 3,140 answers. The suffix is carried (it narrows `nextAccessors`) but, by default, not compared.
 */
class TaintMarkFieldUnfoldRequest(
    val method: MethodEntryPoint,
    val fact: InitialFactAp,
    val mark: TaintMarkAccessor,
    val suffix: FinalFactAp.Delta?
) : SideEffectKind {
    fun copy(suffix: FinalFactAp.Delta?): TaintMarkFieldUnfoldRequest =
        TaintMarkFieldUnfoldRequest(method, fact, mark, suffix)

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is TaintMarkFieldUnfoldRequest) return false
        if (mark != other.mark) return false
        if (method != other.method) return false
        if (fact != other.fact) return false
        return !UnfoldClimbBound.suffixInKey || suffix == other.suffix
    }

    override fun hashCode(): Int {
        var h = method.hashCode()
        h = 31 * h + fact.hashCode()
        h = 31 * h + mark.hashCode()
        if (UnfoldClimbBound.suffixInKey) h = 31 * h + (suffix?.hashCode() ?: 0)
        return h
    }

    override fun toString(): String =
        "TaintMarkFieldUnfoldRequest(method=$method, fact=$fact, mark=$mark, suffix=$suffix)"
}

data class DefaultFactWithMarkAfterAnyFieldResolver(
    private val method: MethodEntryPoint,
    private val initialFact: InitialFactAp,
    private val addSideEffect: (InitialFactAp, SideEffectKind) -> Unit
): FactWithMarkAfterAnyAccessorResolver {
    override fun resolve(mark: TaintMarkAccessor) {
        addSideEffect(initialFact, TaintMarkFieldUnfoldRequest(method, initialFact, mark, suffix = null))
    }

    companion object {
        fun createMarkAfterAccessorResolver(
            method: MethodEntryPoint,
            initialFacts: Set<InitialFactAp>,
            addSideEffect: (InitialFactAp, SideEffectKind) -> Unit
        ): DefaultFactWithMarkAfterAnyFieldResolver? {
            // 0 or 2+ facts implies that we have no abstraction
            if (initialFacts.size != 1) return null
            return DefaultFactWithMarkAfterAnyFieldResolver(method, initialFacts.first(), addSideEffect)
        }
    }
}
