package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

sealed interface BaseOnlyFinalDelta : FinalFactAp.Delta

data object BaseOnlyEmptyFinalDelta : BaseOnlyFinalDelta {
    override val isEmpty: Boolean get() = true
    override fun startsWithAccessor(accessor: Accessor): Boolean = false
    override fun getStartAccessors(): Set<Accessor> = emptySet()
    override fun getAllAccessors(): Set<Accessor> = emptySet()
    override fun readAccessor(accessor: Accessor): FinalFactAp.Delta? = null
    override fun isAbstract(): Boolean = true
}

class BaseOnlyNodeFinalDelta(
    val manager: BaseOnlyApManager,
    val access: BaseOnlyAccess,
) : BaseOnlyFinalDelta {
    override val isEmpty: Boolean get() = false

    override fun startsWithAccessor(accessor: Accessor): Boolean = manager.startsWithAccessor(access, accessor)

    override fun getStartAccessors(): Set<Accessor> = manager.startAccessors(access)

    override fun getAllAccessors(): Set<Accessor> = manager.allAccessors(access)

    override fun readAccessor(accessor: Accessor): FinalFactAp.Delta? =
        manager.readAccess(access, accessor)?.let { BaseOnlyNodeFinalDelta(manager, it) }

    override fun isAbstract(): Boolean = access.isRootAbstract

    override fun equals(other: Any?): Boolean =
        this === other || (other is BaseOnlyNodeFinalDelta && access == other.access)

    override fun hashCode(): Int = access.hashCode()

    override fun toString(): String = manager.renderAccess(access)
}

sealed interface BaseOnlyInitialDelta : InitialFactAp.Delta

data object BaseOnlyEmptyInitialDelta : BaseOnlyInitialDelta {
    override val isEmpty: Boolean get() = true
    override fun startsWithAccessor(accessor: Accessor): Boolean = false
    override fun getStartAccessors(): Set<Accessor> = emptySet()
    override fun getAllAccessors(): Set<Accessor> = emptySet()
    override fun readAccessor(accessor: Accessor): InitialFactAp.Delta? = null
    override fun isAbstract(): Boolean = true
    override fun concat(other: InitialFactAp.Delta): InitialFactAp.Delta = other
}

class BaseOnlyNodeInitialDelta(
    val manager: BaseOnlyApManager,
    val access: BaseOnlyAccess,
) : BaseOnlyInitialDelta {
    override val isEmpty: Boolean get() = false

    override fun startsWithAccessor(accessor: Accessor): Boolean = manager.startsWithAccessor(access, accessor)

    override fun getStartAccessors(): Set<Accessor> = manager.startAccessors(access)

    override fun getAllAccessors(): Set<Accessor> = manager.allAccessors(access)

    override fun readAccessor(accessor: Accessor): InitialFactAp.Delta? =
        manager.readAccess(access, accessor)?.let { BaseOnlyNodeInitialDelta(manager, it) }

    override fun isAbstract(): Boolean = access.isRootAbstract

    override fun concat(other: InitialFactAp.Delta): InitialFactAp.Delta = when (other) {
        BaseOnlyEmptyInitialDelta -> this
        is BaseOnlyNodeInitialDelta -> {
            BaseOnlyNodeInitialDelta(
                manager,
                BaseOnlyAccessOps.append(access, other.access)
                    ?: error("static-first invariant violated: delta compose")
            )
        }
        else -> error("Unexpected delta: $other")
    }

    override fun equals(other: Any?): Boolean =
        this === other || (other is BaseOnlyNodeInitialDelta && access == other.access)

    override fun hashCode(): Int = access.hashCode()

    override fun toString(): String = manager.renderAccess(access)
}
