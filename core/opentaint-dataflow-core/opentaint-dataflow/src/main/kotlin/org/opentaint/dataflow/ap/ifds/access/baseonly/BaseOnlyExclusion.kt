package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTypeInfoAccessor

fun slotOfIdx(idx: AccessorIdx): Int = when {
    idx.isStaticAccessor() -> 0
    idx.isFieldAccessor() || idx == ELEMENT_ACCESSOR_IDX -> 1
    else -> 2
}

fun IntOpenHashSet.excludesIdx(idx: AccessorIdx): Boolean =
    contains(idx) || (idx.isTypeInfoAccessor() && contains(TYPE_INFO_GROUP_ACCESSOR_IDX))

class BaseOnlyExclusionMerge(
    @JvmField val value: Any,
    @JvmField val grew: Boolean,
)

object BaseOnlyExclusion {
    val EMPTY: Any = Any()
    val UNIVERSE: Any = Any()
}

object BaseOnlyExclusionOps {
    fun fromExclusionSet(ex: ExclusionSet, interner: AccessorInterner, apSlot: Int): Any = when (ex) {
        ExclusionSet.Empty -> BaseOnlyExclusion.EMPTY
        ExclusionSet.Universe -> BaseOnlyExclusion.UNIVERSE
        is ExclusionSet.Concrete -> {
            val set = IntOpenHashSet(ex.set.size)
            for (accessor in ex.set) {
                val idx = interner.index(accessor)
                if (slotOfIdx(idx) >= apSlot) set.add(idx)
            }
            if (set.isEmpty()) BaseOnlyExclusion.EMPTY else set
        }
    }

    fun toExclusionSet(value: Any, interner: AccessorInterner): ExclusionSet = when (value) {
        BaseOnlyExclusion.EMPTY -> ExclusionSet.Empty
        BaseOnlyExclusion.UNIVERSE -> ExclusionSet.Universe
        else -> {
            val set = value.asIntSet()
            var result: ExclusionSet = ExclusionSet.Empty
            val iterator = set.iterator()
            while (iterator.hasNext()) {
                val accessor = interner.accessor(iterator.nextInt()) ?: continue
                result = result.add(accessor)
            }
            result
        }
    }

    fun contains(value: Any, idx: AccessorIdx): Boolean = when (value) {
        BaseOnlyExclusion.EMPTY -> false
        BaseOnlyExclusion.UNIVERSE -> true
        else -> value.asIntSet().excludesIdx(idx)
    }

    fun mergeInPlace(cur: Any, incoming: Any): BaseOnlyExclusionMerge = when {
        cur === BaseOnlyExclusion.UNIVERSE -> BaseOnlyExclusionMerge(cur, grew = false)
        incoming === BaseOnlyExclusion.UNIVERSE -> BaseOnlyExclusionMerge(BaseOnlyExclusion.UNIVERSE, grew = true)
        incoming === BaseOnlyExclusion.EMPTY -> BaseOnlyExclusionMerge(cur, grew = false)
        cur === BaseOnlyExclusion.EMPTY -> BaseOnlyExclusionMerge(incoming, grew = true)
        else -> {
            val curSet = cur.asIntSet()
            val grew = curSet.addAll(incoming.asIntSet())
            BaseOnlyExclusionMerge(curSet, grew)
        }
    }

    private fun Any.asIntSet(): IntOpenHashSet {
        assert(this is IntOpenHashSet) { "BaseOnly exclusion value must be EMPTY, UNIVERSE, or IntOpenHashSet, got ${this::class}" }
        return this as IntOpenHashSet
    }
}
