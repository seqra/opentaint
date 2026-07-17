package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTaintMarkAccessor

fun BaseOnlyApManager.startsWithAccessor(access: BaseOnlyAccess, accessor: Accessor): Boolean =
    BaseOnlyAccessOps.startsWith(access, interner.index(accessor))

fun BaseOnlyApManager.startAccessors(access: BaseOnlyAccess): Set<Accessor> {
    val head = access.headOrNull ?: return emptySet()
    val concreteHead = interner.accessor(head) ?: error("Accessor not found: $head")
    return if (access.hasSemanticMark && access.suffixIdx.isTaintMarkAccessor()) {
        setOf(AnyAccessor, concreteHead)
    } else {
        setOf(concreteHead)
    }
}

fun BaseOnlyApManager.allAccessors(access: BaseOnlyAccess): Set<Accessor> =
    buildSet { access.forEachAccessorIdx { add(interner.accessor(it) ?: error("Accessor not found: $it")) } }

fun BaseOnlyApManager.readAccess(access: BaseOnlyAccess, accessor: Accessor): BaseOnlyAccess? =
    BaseOnlyAccessOps.read(access, interner.index(accessor))
