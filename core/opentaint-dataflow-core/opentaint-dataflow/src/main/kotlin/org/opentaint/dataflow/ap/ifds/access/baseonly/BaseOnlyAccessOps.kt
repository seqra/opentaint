package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor

class BaseOnlySplit(
    @JvmField val matched: BaseOnlyAccess,
    @JvmField val delta: BaseOnlyAccess,
)

object BaseOnlyAccessOps {
    val empty: BaseOnlyAccess get() = EMPTY_ACCESS
    val abstractEmpty: BaseOnlyAccess get() = ABSTRACT_EMPTY_ACCESS
    val finalAccess: BaseOnlyAccess get() = FINAL_ACCESS

    fun build(accessors: IntArray, isAbstract: Boolean): BaseOnlyAccess {
        var staticIdx = NO_ACCESSOR
        var fieldIdx = NO_ACCESSOR
        var semanticIdx = NO_ACCESSOR
        var hasFinal = false
        for (idx in accessors) {
            when {
                idx.isStaticAccessor() -> staticIdx = idx
                idx.isFieldAccessor() || idx == ELEMENT_ACCESSOR_IDX -> fieldIdx = idx
                idx == ANY_ACCESSOR_IDX || idx == TYPE_INFO_GROUP_ACCESSOR_IDX -> {}
                idx == FINAL_ACCESSOR_IDX -> hasFinal = true
                else -> if (semanticIdx < 0) semanticIdx = idx
            }
        }
        val suffixIdx = when {
            semanticIdx >= 0 -> semanticIdx
            hasFinal -> FINAL_ACCESSOR_IDX
            isAbstract -> ABSTRACT_MARK
            else -> NO_ACCESSOR
        }
        return packNormalized(staticIdx, fieldIdx, suffixIdx)
    }

    fun abstractAt(staticIdx: AccessorIdx, fieldIdx: AccessorIdx, apSlot: Int): BaseOnlyAccess = when (apSlot) {
        0 -> packNormalized(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR)
        1 -> packNormalized(staticIdx, ABSTRACT_MARK, NO_ACCESSOR)
        else -> packNormalized(staticIdx, fieldIdx, ABSTRACT_MARK)
    }

    fun collapse(access: BaseOnlyAccess): BaseOnlyAccess = when (access.apSlot) {
        0 -> packNormalized(NO_ACCESSOR, access.fieldIdx, access.suffixIdx)
        1 -> packNormalized(access.staticIdx, NO_ACCESSOR, access.suffixIdx)
        2 -> packNormalized(access.staticIdx, access.fieldIdx, COLLAPSED_MARK)
        else -> access
    }

    fun restoreAbstraction(access: BaseOnlyAccess): BaseOnlyAccess =
        if (access.suffixIdx == COLLAPSED_MARK) packNormalized(access.staticIdx, access.fieldIdx, ABSTRACT_MARK)
        else access

    fun prepend(access: BaseOnlyAccess, idx: AccessorIdx, fieldSensitive: Boolean): BaseOnlyAccess = when {
        idx == TYPE_INFO_GROUP_ACCESSOR_IDX -> access
        idx.isStaticAccessor() -> packNormalized(idx, access.fieldIdx, access.suffixIdx)
        structural(idx) ->
            if (!fieldSensitive || idx.isAnyIdx()) access
            else packNormalized(access.staticIdx, idx, access.suffixIdx)
        else -> packNormalized(access.staticIdx, access.fieldIdx, idx)
    }

    fun read(access: BaseOnlyAccess, idx: AccessorIdx): BaseOnlyAccess? = when (headRead(access, idx)) {
        HeadRead.NONE -> null
        HeadRead.KEEP -> access
        HeadRead.TAIL -> tail(access)
    }

    fun startsWith(access: BaseOnlyAccess, idx: AccessorIdx): Boolean = headRead(access, idx) != HeadRead.NONE

    fun clear(access: BaseOnlyAccess, idx: AccessorIdx): BaseOnlyAccess? {
        val head = access.firstAccessorOrNull ?: return access
        val matched = if (idx.isAnyIdx()) head.isStructuralIdx() else head == idx
        return if (matched) null else access
    }

    fun append(prefix: BaseOnlyAccess, suffix: BaseOnlyAccess): BaseOnlyAccess? {
        if (suffix.staticIdx >= 0 && prefix.coreSize > 0) return null
        val prefixStaticConcrete = if (prefix.staticIdx == ABSTRACT_MARK) NO_ACCESSOR else prefix.staticIdx
        val prefixFieldConcrete = if (prefix.fieldIdx == ABSTRACT_MARK) NO_ACCESSOR else prefix.fieldIdx
        val staticIdx = if (suffix.staticIdx >= 0) suffix.staticIdx else prefixStaticConcrete
        val fieldIdx = when {
            suffix.fieldIdx >= 0 -> suffix.fieldIdx
            suffix.fieldIdx == ABSTRACT_MARK -> ABSTRACT_MARK
            else -> prefixFieldConcrete
        }
        val suffixIdx =
            if (fieldIdx == ABSTRACT_MARK) NO_ACCESSOR
            else combineTerminal(prefix, suffix)
        return packNormalized(staticIdx, fieldIdx, suffixIdx)
    }

    fun appendFinal(prefix: BaseOnlyAccess, suffix: BaseOnlyAccess): BaseOnlyAccess? {
        if (suffix.isEmpty) return prefix
        val suffixFirst = slotOfFirstAccessor(suffix)

        return when (prefix.apSlot) {
            0 -> {
                if (suffixFirst != 0) return null
                packNormalized(suffix.staticIdx, suffix.fieldIdx, suffix.suffixIdx)
            }

            1 -> {
                if (suffixFirst != 1) return null
                packNormalized(prefix.staticIdx, suffix.fieldIdx, suffix.suffixIdx)
            }

            2 -> when (suffixFirst) {
                2 -> packNormalized(prefix.staticIdx, prefix.fieldIdx, suffix.suffixIdx)

                // note: we have [any] after prefix field, which consumes the suffix.field
                1 -> packNormalized(prefix.staticIdx, prefix.fieldIdx, suffix.suffixIdx)

                else -> null
            }

            else -> null
        }
    }

    private fun slotOfFirstAccessor(a: BaseOnlyAccess): Int = when {
        a.staticIdx != NO_ACCESSOR -> 0
        a.fieldIdx != NO_ACCESSOR -> 1
        a.suffixIdx != NO_ACCESSOR -> 2
        else -> -1
    }

    private fun slotVal(a: BaseOnlyAccess, slot: Int): AccessorIdx = when (slot) {
        0 -> a.staticIdx
        1 -> a.fieldIdx
        else -> a.suffixIdx
    }

    private fun covers(pattern: BaseOnlyAccess, x: BaseOnlyAccess): Boolean {
        if (pattern == x) return true
        if (!pattern.hasAp) return false
        val k = pattern.apSlot
        for (j in 0 until k) if (slotVal(x, j) != slotVal(pattern, j)) return false
        if (slotVal(x, k) == NO_ACCESSOR) return false
        if (x.hasAp && x.apSlot < k) return false
        return true
    }

    fun matchPrefix(final: BaseOnlyAccess, initial: BaseOnlyAccess): BaseOnlyMatch {
        if (final == initial) return IDENTITY_MATCH
        if (!covers(initial, final)) return NO_MATCH
        return BaseOnlyMatch(emptyDelta = false, hasSuffix = true, suffix = dropCorePrefix(final, initial.apSlot))
    }

    fun splitConcreteInitial(final: BaseOnlyAccess, initial: BaseOnlyAccess): BaseOnlySplit? {
        if (initial.hasAp) return null
        return when (final.apSlot) {
            0 -> BaseOnlySplit(final, initial)
            1 -> {
                if (!staticsCompatible(initial.staticIdx, final.staticIdx)) return null
                BaseOnlySplit(final, packNormalized(NO_ACCESSOR, initial.fieldIdx, initial.suffixIdx))
            }
            2 -> {
                if (!staticsCompatible(initial.staticIdx, final.staticIdx)) return null
                if (!fieldsCompatible(initial.fieldIdx, final.fieldIdx)) return null
                BaseOnlySplit(final, packNormalized(NO_ACCESSOR, NO_ACCESSOR, initial.suffixIdx))
            }
            else -> null
        }
    }

    fun splitDelta(
        fact: BaseOnlyAccess,
        pattern: BaseOnlyAccess,
        manager: BaseOnlyApManager,
        exclusions: ExclusionSet,
    ): List<Pair<BaseOnlyAccess, BaseOnlyInitialDelta>> {
        if (fact.hasAp) {
            if (!containsAccess(pattern, fact)) return emptyList()

            // A suffix-abstract fact with a concrete field refines a field-abstract summary
            // pattern. Preserve that representable field so mapping the summary initial and
            // concatenating the delta reconstructs the caller fact:
            // <field-*> matched against field.* must retain delta field.*.
            if (pattern.apSlot == 1 && fact.apSlot == 2 && fact.fieldIdx >= 0) {
                val delta = dropCorePrefix(fact, pattern.apSlot)
                if (manager.suffixExcluded(delta, exclusions)) return emptyList()
                return listOf(pattern to BaseOnlyNodeInitialDelta(manager, delta))
            }

            return listOf(pattern to BaseOnlyEmptyInitialDelta)
        }

        if (pattern.hasAp) {
            val split = splitConcreteInitial(pattern, fact) ?: return emptyList()
            if (manager.suffixExcluded(split.delta, exclusions)) return emptyList()
            return listOf(split.matched to BaseOnlyNodeInitialDelta(manager, split.delta))
        }

        if (containsAccess(pattern, fact)) {
            return listOf(pattern to BaseOnlyEmptyInitialDelta)
        }
        return emptyList()
    }

    fun containsAccess(final: BaseOnlyAccess, initial: BaseOnlyAccess): Boolean {
        if (final == initial) return true

        if (final.staticIdx == ABSTRACT_MARK) return true
        if (!staticsCompatible(final.staticIdx, initial.staticIdx)) return false

        if (final.fieldIdx == ABSTRACT_MARK) return true
        if (!fieldsCompatible(final.fieldIdx, initial.fieldIdx)) return false

        if (final.suffixIdx == ABSTRACT_MARK) return true
        if (final.suffixIdx == NO_ACCESSOR) return false
        return final.suffixIdx == initial.suffixIdx
    }

    fun equalToInitial(final: BaseOnlyAccess, initial: BaseOnlyAccess): Boolean {
        if (initial.staticIdx != final.staticIdx) return false
        if (initial.fieldIdx != final.fieldIdx) return false
        val initialSemantic = if (initial.hasSemanticMark) initial.suffixIdx else NO_ACCESSOR
        val finalSemantic = if (final.hasSemanticMark) final.suffixIdx else NO_ACCESSOR
        if (initialSemantic != finalSemantic) return false
        val terminalsAgree =
            if (initial.hasTerminalAccessor) !final.isSuffixAbstract
            else final.isSuffixAbstract == initial.isSuffixAbstract
        return terminalsAgree
    }

    private enum class HeadRead { NONE, KEEP, TAIL }

    private fun headRead(access: BaseOnlyAccess, idx: AccessorIdx): HeadRead {
        if (idx == TYPE_INFO_GROUP_ACCESSOR_IDX) return if (access.hasTypeInfoSuffix) HeadRead.KEEP else HeadRead.NONE
        if (access.staticIdx >= 0) return if (idx == access.staticIdx) HeadRead.TAIL else HeadRead.NONE
        if (access.staticIdx == ABSTRACT_MARK) return HeadRead.NONE
        if (access.fieldIdx >= 0) return if (idx == access.fieldIdx || idx.isAnyIdx()) HeadRead.TAIL else HeadRead.NONE
        if (access.fieldIdx == ABSTRACT_MARK) return HeadRead.NONE
        return when {
            access.hasSemanticMark -> when {
                structural(idx) -> HeadRead.KEEP
                idx == access.suffixIdx -> HeadRead.TAIL
                else -> HeadRead.NONE
            }
            access.suffixIdx == ABSTRACT_MARK -> if (structural(idx)) HeadRead.KEEP else HeadRead.NONE
            access.isCollapsed -> if (structural(idx)) HeadRead.KEEP else HeadRead.NONE
            access.suffixIdx == FINAL_ACCESSOR_IDX -> if (idx == FINAL_ACCESSOR_IDX) HeadRead.KEEP else HeadRead.NONE
            else -> HeadRead.NONE
        }
    }

    private fun tail(access: BaseOnlyAccess): BaseOnlyAccess = when {
        access.staticIdx >= 0 -> packNormalized(NO_ACCESSOR, access.fieldIdx, access.suffixIdx)
        access.fieldIdx >= 0 -> packNormalized(NO_ACCESSOR, NO_ACCESSOR, access.suffixIdx)
        access.hasSemanticMark -> packNormalized(NO_ACCESSOR, NO_ACCESSOR, FINAL_ACCESSOR_IDX)
        else -> EMPTY_ACCESS
    }

    private fun combineTerminal(prefix: BaseOnlyAccess, suffix: BaseOnlyAccess): AccessorIdx = when {
        prefix.hasSemanticMark -> prefix.suffixIdx
        suffix.hasSemanticMark -> suffix.suffixIdx
        suffix.suffixIdx == FINAL_ACCESSOR_IDX -> FINAL_ACCESSOR_IDX
        suffix.suffixIdx == ABSTRACT_MARK -> ABSTRACT_MARK
        prefix.suffixIdx == ABSTRACT_MARK -> ABSTRACT_MARK
        else -> NO_ACCESSOR
    }

    private fun dropCorePrefix(access: BaseOnlyAccess, dropSlots: Int): BaseOnlyAccess {
        val staticIdx = if (dropSlots <= 0) access.staticIdx else NO_ACCESSOR
        val fieldIdx = if (dropSlots <= 1) access.fieldIdx else NO_ACCESSOR
        return packNormalized(staticIdx, fieldIdx, access.suffixIdx)
    }

    private fun structural(idx: AccessorIdx): Boolean = idx.isStructuralIdx() || idx.isAnyIdx()

    private fun staticsCompatible(a: AccessorIdx, b: AccessorIdx): Boolean = a == b

    private fun fieldsCompatible(a: AccessorIdx, b: AccessorIdx): Boolean =
        a == NO_ACCESSOR || b == NO_ACCESSOR || a == b

    private fun packNormalized(staticIdx: AccessorIdx, fieldIdx: AccessorIdx, suffixIdx: AccessorIdx): BaseOnlyAccess {
        val apEarlier = staticIdx == ABSTRACT_MARK || fieldIdx == ABSTRACT_MARK
        val normalizedSuffix =
            if (suffixIdx == NO_ACCESSOR && !apEarlier && (staticIdx >= 0 || fieldIdx >= 0)) ABSTRACT_MARK
            else suffixIdx
        return packBaseOnlyAccess(staticIdx, fieldIdx, normalizedSuffix)
    }

    private val NO_MATCH = BaseOnlyMatch(emptyDelta = false, hasSuffix = false, suffix = EMPTY_ACCESS)
    private val IDENTITY_MATCH = BaseOnlyMatch(emptyDelta = true, hasSuffix = false, suffix = EMPTY_ACCESS)
}
