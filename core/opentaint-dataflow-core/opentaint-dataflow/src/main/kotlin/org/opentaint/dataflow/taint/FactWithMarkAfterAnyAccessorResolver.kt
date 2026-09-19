package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

interface FactWithMarkAfterAnyAccessorResolver {
    fun resolve(mark: TaintMarkAccessor)
}

/**
 * A request identity, and identity is all it is used for: it is the key of the per-frame
 * `ConcurrentHashMap<SideEffectKind, ExclusionSet>` in
 * [org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.SideEffectExclusionMergingStorage],
 * of two `groupBy` maps on the store path, and of the `HashSet<Sequent>` the handler returns --
 * so one climb post hashes it several times, and the storage's whole job is to answer "seen it".
 *
 * As a data class that hash walked six objects and summed a `hashCode` over every accessor in
 * [suffix] on every one of those calls, which a stack-sampling profile of
 * `AnyFieldUnfoldDemandAnalysisTest` put at the top of the analysis. The fields are immutable, so
 * the hash is computed once, exactly as [org.opentaint.dataflow.ap.ifds.ExclusionSet.Concrete] and
 * `AccessTree.AccessNode` already do. Same equivalence relation, same hash values.
 */
class TaintMarkFieldUnfoldRequest(
    val method: MethodEntryPoint,
    val fact: InitialFactAp,
    val mark: TaintMarkAccessor,
    val suffix: Set<Accessor>?
) : SideEffectKind {
    private val hash: Int = run {
        var result = method.hashCode()
        result = 31 * result + fact.hashCode()
        result = 31 * result + mark.hashCode()
        result = 31 * result + (suffix?.hashCode() ?: 0)
        result
    }

    fun copy(suffix: Set<Accessor>?): TaintMarkFieldUnfoldRequest =
        TaintMarkFieldUnfoldRequest(method, fact, mark, suffix)

    override fun hashCode(): Int = hash

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is TaintMarkFieldUnfoldRequest) return false

        if (hash != other.hash) return false
        if (mark != other.mark) return false
        if (suffix != other.suffix) return false
        if (fact != other.fact) return false
        return method == other.method
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
