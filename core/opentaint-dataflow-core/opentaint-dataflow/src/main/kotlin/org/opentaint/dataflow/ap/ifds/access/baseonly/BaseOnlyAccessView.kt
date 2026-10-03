package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTaintMarkAccessor

fun BaseOnlyApManager.startsWithAccessor(access: BaseOnlyAccess, accessor: Accessor): Boolean =
    BaseOnlyAccessOps.startsWith(access, interner.index(accessor))

fun BaseOnlyApManager.startAccessors(access: BaseOnlyAccess): Set<Accessor> {
    val staticIdx = access.staticIdx
    if (staticIdx >= 0) return setOf(accessor(staticIdx))
    if (staticIdx == ABSTRACT_MARK) return emptySet()

    val fieldIdx = access.fieldIdx
    if (fieldIdx >= 0) {
        return setOf(accessor(fieldIdx))
    }
    if (fieldIdx == ABSTRACT_MARK) return emptySet()

    return when {
        access.hasTypeInfoSuffix -> terminalStarts(
            access,
            TypeInfoGroupAccessor,
            accessor(access.suffixIdx),
        ) + AnyAccessor
        access.hasSemanticMark && access.suffixIdx.isTaintMarkAccessor() -> terminalStarts(
            access,
            ValueAccessor,
            accessor(access.suffixIdx),
        ) + AnyAccessor
        access.isSuffixAbstract || access.isCollapsed -> setOf(AnyAccessor)
        access.hasSemanticMark -> setOf(AnyAccessor, accessor(access.suffixIdx))
        access.suffixIdx >= 0 -> setOf(accessor(access.suffixIdx))
        else -> emptySet()
    }
}

fun BaseOnlyApManager.allAccessors(access: BaseOnlyAccess): Set<Accessor> =
    buildSet {
        if (access.hasSemanticMark && access.suffixIdx.isTaintMarkAccessor() &&
            access.valueAccessorState == BaseOnlyValueAccessorState.Value
        ) add(ValueAccessor)
        access.forEachAccessorIdx { idx ->
            val accessor = accessor(idx)
            if (accessor != AnyAccessor) add(accessor)
        }
    }

private fun terminalStarts(
    access: BaseOnlyAccess,
    wrapper: Accessor,
    suffix: Accessor,
): Set<Accessor> = when (access.valueAccessorState) {
    BaseOnlyValueAccessorState.Normal -> setOf(suffix)
    BaseOnlyValueAccessorState.Value -> setOf(wrapper)
}

fun BaseOnlyApManager.readAccess(access: BaseOnlyAccess, accessor: Accessor): BaseOnlyAccess? =
    BaseOnlyAccessOps.read(access, interner.index(accessor))

private fun BaseOnlyApManager.accessor(idx: Int): Accessor =
    interner.accessor(idx) ?: error("Accessor not found: $idx")
