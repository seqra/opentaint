package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

class BaseOnlyFinalFactAp(
    val manager: BaseOnlyApManager,
    override val base: AccessPathBase,
    val access: BaseOnlyAccess,
    override val exclusions: ExclusionSet,
) : FinalFactAp {
    init {
        require(!access.isEmpty) { "empty is not a fact: $base" }
    }

    override val size: Int get() = access.size
    override val depth: Int get() = access.size

    override fun isAbstract(): Boolean = access.hasAp

    override fun rebase(newBase: AccessPathBase): FinalFactAp =
        BaseOnlyFinalFactAp(manager, newBase, BaseOnlyAccessOps.restoreAbstraction(access), exclusions)

    override fun exclude(accessor: Accessor): FinalFactAp =
        BaseOnlyFinalFactAp(manager, base, access, exclusions.add(accessor))

    override fun replaceExclusions(exclusions: ExclusionSet): FinalFactAp =
        BaseOnlyFinalFactAp(manager, base, access, exclusions)

    private fun rewrap(newAccess: BaseOnlyAccess): BaseOnlyFinalFactAp =
        BaseOnlyFinalFactAp(manager, base, newAccess, exclusions)

    override fun startsWithAccessor(accessor: Accessor): Boolean = manager.startsWithAccessor(access, accessor)

    override fun getStartAccessors(): Set<Accessor> = manager.startAccessors(access)

    override fun getAllAccessors(): Set<Accessor> = manager.allAccessors(access)

    override fun readAccessor(accessor: Accessor): FinalFactAp? = manager.readAccess(access, accessor)?.let(::rewrap)

    override fun prependAccessor(accessor: Accessor): FinalFactAp =
        rewrap(BaseOnlyAccessOps.prepend(access, manager.interner.index(accessor), manager.fieldSensitive))

    override fun clearAccessor(accessor: Accessor): FinalFactAp? =
        BaseOnlyAccessOps.clear(access, manager.interner.index(accessor))?.let(::rewrap)

    override fun removeAbstraction(): FinalFactAp? =
        BaseOnlyAccessOps.collapse(access).takeIf { !it.isEmpty }?.let(::rewrap)

    override fun abstractOnly(): FinalFactAp {
        val resultAccess = access.withBaseOnlyAccessUnpacked { s, f, _ ->
            when {
                s == ABSTRACT_MARK -> packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR)
                f == ABSTRACT_MARK -> packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)
                else -> packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, ABSTRACT_MARK)
            }
        }
        return rewrap(resultAccess)
    }

    override fun filterFact(filter: FactTypeChecker.FactApFilter): FinalFactAp? =
        if (accessPathAccepted(filter)) this else null

    override fun filterFact(filter: FactTypeChecker.FactCompatibilityFilter): FinalFactAp? {
        if (filter is FactTypeChecker.AlwaysCompatibleFilter) return this
        access.forEachAccessorIdx { idx ->
            val accessor = manager.interner.accessor(idx) ?: error("Accessor not found: $idx")
            if (filter.check(accessor) == FactTypeChecker.CompatibilityFilterResult.NotCompatible) return null
        }
        return this
    }

    private fun accessPathAccepted(filter: FactTypeChecker.FactApFilter): Boolean {
        var current = filter
        access.forEachAccessorIdx { idx ->
            val accessor = manager.interner.accessor(idx) ?: error("Accessor not found: $idx")
            when (val result = current.check(accessor)) {
                FactTypeChecker.FilterResult.Accept -> return true
                FactTypeChecker.FilterResult.Reject -> return false
                is FactTypeChecker.FilterResult.FilterNext -> current = result.filter
            }
        }
        return true
    }

    override fun contains(factAp: InitialFactAp): Boolean {
        factAp as BaseOnlyInitialFactAp
        if (base != factAp.base) return false
        return BaseOnlyAccessOps.containsAccess(access, factAp.access)
    }

    override fun equalTo(factAp: InitialFactAp): Boolean {
        factAp as BaseOnlyInitialFactAp
        if (base != factAp.base) return false
        return BaseOnlyAccessOps.equalToInitial(access, factAp.access)
    }

    override fun delta(other: InitialFactAp): List<FinalFactAp.Delta> {
        other as BaseOnlyInitialFactAp
        val match = BaseOnlyAccessOps.matchPrefix(access, other.access)
        val result = ArrayList<FinalFactAp.Delta>(2)
        if (match.emptyDelta) result.add(BaseOnlyEmptyFinalDelta)
        if (match.hasSuffix && !manager.suffixExcluded(match.suffix, other.exclusions)) {
            result.add(BaseOnlyNodeFinalDelta(manager, match.suffix))
        }
        return result
    }

    override fun concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp? =
        when (val d = delta as BaseOnlyFinalDelta) {
            BaseOnlyEmptyFinalDelta -> this
            is BaseOnlyNodeFinalDelta -> BaseOnlyAccessOps.appendFinal(access, d.access, manager.fieldSensitive)?.let(::rewrap)
        }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is BaseOnlyFinalFactAp) return false
        return base == other.base && access == other.access && exclusions == other.exclusions
    }

    override fun hashCode(): Int {
        var result = base.hashCode()
        result = 31 * result + access.hashCode()
        result = 31 * result + exclusions.hashCode()
        return result
    }

    override fun toString(): String = "$base${manager.renderAccess(access)}/$exclusions"
}
