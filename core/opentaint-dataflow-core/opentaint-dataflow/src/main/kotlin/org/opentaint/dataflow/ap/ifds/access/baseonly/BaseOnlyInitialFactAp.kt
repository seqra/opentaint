package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

class BaseOnlyInitialFactAp(
    val manager: BaseOnlyApManager,
    override val base: AccessPathBase,
    val access: BaseOnlyAccess,
    override val exclusions: ExclusionSet,
) : InitialFactAp {
    init {
        BaseOnlyAccessOps.requireCanonical(access)
    }

    override val size: Int get() = access.size
    override val depth: Int get() = access.size

    override fun isAbstract(): Boolean = access.hasAp

    override fun rebase(newBase: AccessPathBase): InitialFactAp =
        BaseOnlyInitialFactAp(manager, newBase, access, exclusions)

    override fun exclude(accessor: Accessor): InitialFactAp =
        BaseOnlyInitialFactAp(manager, base, access, exclusions.add(accessor))

    override fun replaceExclusions(exclusions: ExclusionSet): InitialFactAp =
        BaseOnlyInitialFactAp(manager, base, access, exclusions)

    private fun rewrap(newAccess: BaseOnlyAccess): BaseOnlyInitialFactAp =
        BaseOnlyInitialFactAp(manager, base, newAccess, exclusions)

    override fun startsWithAccessor(accessor: Accessor): Boolean = manager.startsWithAccessor(access, accessor)

    override fun getStartAccessors(): Set<Accessor> = manager.startAccessors(access)

    override fun getAllAccessors(): Set<Accessor> = manager.allAccessors(access)

    override fun readAccessor(accessor: Accessor): InitialFactAp? = manager.readAccess(access, accessor)?.let(::rewrap)

    override fun prependAccessor(accessor: Accessor): InitialFactAp =
        rewrap(BaseOnlyAccessOps.prepend(access, manager.interner.index(accessor), manager.fieldSensitive))

    override fun clearAccessor(accessor: Accessor): InitialFactAp? =
        BaseOnlyAccessOps.clear(access, manager.interner.index(accessor))?.let(::rewrap)

    override fun compatibilityFilter(typeChecker: FactTypeChecker): FactTypeChecker.FactCompatibilityFilter =
        typeChecker.accessPathCompatibilityFilter(
            buildList { access.forEachAccessorIdx { add(manager.interner.accessor(it) ?: error("Accessor not found: $it")) } }
        )

    override fun splitDelta(other: FinalFactAp): List<Pair<InitialFactAp, InitialFactAp.Delta>> {
        other as BaseOnlyFinalFactAp
        if (base != other.base) return emptyList()

        return BaseOnlyAccessOps.splitDelta(access, other.access, manager, other.exclusions)
            .map { (f, delta) -> rewrap(f) to delta }
    }

    override fun concat(delta: InitialFactAp.Delta): InitialFactAp =
        when (val d = delta as BaseOnlyInitialDelta) {
            BaseOnlyEmptyInitialDelta -> this
            is BaseOnlyNodeInitialDelta -> {
                rewrap(
                    BaseOnlyAccessOps.append(access, d.access)
                        ?: error("static-first invariant violated: initial concat")
                )
            }
        }

    override fun contains(factAp: InitialFactAp): Boolean {
        factAp as BaseOnlyInitialFactAp
        if (base != factAp.base) return false
        return BaseOnlyAccessOps.matchPrefix(access, factAp.access).emptyDelta
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is BaseOnlyInitialFactAp) return false
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
