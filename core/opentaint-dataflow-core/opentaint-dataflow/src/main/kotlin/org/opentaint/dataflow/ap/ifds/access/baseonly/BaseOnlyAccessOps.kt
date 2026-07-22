package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.VALUE_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTypeInfoAccessor

class BaseOnlySplit(
    @JvmField val matched: BaseOnlyAccess,
    @JvmField val delta: BaseOnlyAccess,
)

object BaseOnlyAccessOps {
    val empty: BaseOnlyAccess get() = EMPTY_ACCESS
    val abstractEmpty: BaseOnlyAccess get() = ABSTRACT_EMPTY_ACCESS
    val finalAccess: BaseOnlyAccess get() = FINAL_ACCESS

    /** Validate the representation boundary without assigning semantics to malformed packed values. */
    fun requireCanonical(
        access: BaseOnlyAccess,
        allowEmpty: Boolean = false,
        allowTransientCollapsed: Boolean = false,
    ): BaseOnlyAccess {
        val staticIdx = access.staticIdx
        val fieldIdx = access.fieldIdx
        val suffixIdx = access.suffixIdx
        val valueAccessorState = access.valueAccessorState

        require(staticIdx == NO_ACCESSOR || staticIdx == ABSTRACT_MARK || staticIdx.isStaticAccessor()) {
            "Invalid BaseOnly static slot: $staticIdx"
        }
        require(
            fieldIdx == NO_ACCESSOR || fieldIdx == ABSTRACT_MARK ||
                fieldIdx.isFieldAccessor() || fieldIdx == ELEMENT_ACCESSOR_IDX
        ) { "Invalid BaseOnly structural slot: $fieldIdx" }
        require(
            suffixIdx == NO_ACCESSOR || suffixIdx == ABSTRACT_MARK ||
                (allowTransientCollapsed && suffixIdx == COLLAPSED_MARK) || suffixIdx == FINAL_ACCESSOR_IDX ||
                (suffixIdx >= 0 && !suffixIdx.isStaticAccessor() && !suffixIdx.isFieldAccessor() &&
                    suffixIdx != ELEMENT_ACCESSOR_IDX && suffixIdx != ANY_ACCESSOR_IDX &&
                    suffixIdx != TYPE_INFO_GROUP_ACCESSOR_IDX && suffixIdx != VALUE_ACCESSOR_IDX)
        ) { "Invalid BaseOnly suffix slot: $suffixIdx" }
        require(access.hasSemanticMark || valueAccessorState == BaseOnlyValueAccessorState.Normal) {
            "A value accessor is only valid before a semantic suffix: $valueAccessorState"
        }
        require(allowTransientCollapsed || !access.isCollapsed) {
            "Collapsed BaseOnly access is a transient flow-function value"
        }
        if (staticIdx == ABSTRACT_MARK) {
            require(fieldIdx == NO_ACCESSOR && suffixIdx == NO_ACCESSOR) {
                "Components after a static abstraction are forbidden"
            }
        }
        if (fieldIdx == ABSTRACT_MARK) {
            require(staticIdx >= 0 || staticIdx == NO_ACCESSOR) { "Invalid prefix before field abstraction" }
            require(suffixIdx == NO_ACCESSOR) { "Components after a field abstraction are forbidden" }
        }
        if (!access.hasAp && (staticIdx >= 0 || fieldIdx >= 0)) {
            require(suffixIdx != NO_ACCESSOR) { "A concrete BaseOnly prefix must terminate or abstract" }
        }
        if (!allowEmpty) require(!access.isEmpty) { "Empty BaseOnly access is not a fact" }
        return access
    }

    fun build(accessors: IntArray, isAbstract: Boolean): BaseOnlyAccess {
        validateBuildGrammar(accessors)
        var staticIdx = NO_ACCESSOR
        var fieldIdx = NO_ACCESSOR
        var semanticIdx = NO_ACCESSOR
        var valueAccessorState = BaseOnlyValueAccessorState.Normal
        var hasFinal = false
        for (idx in accessors) {
            when {
                idx.isStaticAccessor() -> {
                    require(staticIdx == NO_ACCESSOR || staticIdx == idx) {
                        "Multiple static accessors in a BaseOnly path: $staticIdx, $idx"
                    }
                    if (staticIdx == NO_ACCESSOR) staticIdx = idx
                }
                idx.isFieldAccessor() || idx == ELEMENT_ACCESSOR_IDX -> {
                    // Canonical BaseOnly retains the outermost structural accessor.
                    if (fieldIdx == NO_ACCESSOR) fieldIdx = idx
                }
                idx == ANY_ACCESSOR_IDX -> Unit
                idx == TYPE_INFO_GROUP_ACCESSOR_IDX -> valueAccessorState = BaseOnlyValueAccessorState.Value
                idx == VALUE_ACCESSOR_IDX -> valueAccessorState = BaseOnlyValueAccessorState.Value
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
        return packNormalized(staticIdx, fieldIdx, suffixIdx, valueAccessorState)
    }

    /** Validate accessor order before projecting a well-formed linear path into three slots. */
    private fun validateBuildGrammar(accessors: IntArray) {
        var staticSeen = false
        var semanticSeen = false
        var finalSeen = false
        var expectType = false
        var expectMark = false
        accessors.forEachIndexed { position, idx ->
            require(!finalSeen) { "Accessor after FinalAccessor at position $position: $idx" }
            if (semanticSeen) {
                require(idx == FINAL_ACCESSOR_IDX) { "Accessor after BaseOnly semantic terminal at position $position: $idx" }
                finalSeen = true
                return@forEachIndexed
            }
            when {
                expectType -> {
                    require(idx.isTypeInfoAccessor()) { "TypeInfoGroupAccessor must be followed by a type accessor" }
                    expectType = false
                    semanticSeen = true
                }
                expectMark -> {
                    require(idx.isTaintMarkAccessor()) { "ValueAccessor must be followed by a taint mark" }
                    expectMark = false
                    semanticSeen = true
                }
                idx.isStaticAccessor() -> {
                    require(position == 0 && !staticSeen) { "Static accessor is only valid once at the path root" }
                    staticSeen = true
                }
                structural(idx) -> Unit
                idx == TYPE_INFO_GROUP_ACCESSOR_IDX -> expectType = true
                idx == VALUE_ACCESSOR_IDX -> expectMark = true
                idx == FINAL_ACCESSOR_IDX -> finalSeen = true
                else -> semanticSeen = true // taint mark or compact type residual
            }
        }
        require(!expectType) { "TypeInfoGroupAccessor requires a following type accessor" }
        require(!expectMark) { "ValueAccessor requires a following taint mark" }
    }

    fun abstractAt(staticIdx: AccessorIdx, fieldIdx: AccessorIdx, apSlot: Int): BaseOnlyAccess {
        require(apSlot in 0..2) { "Invalid BaseOnly abstraction slot: $apSlot" }
        return when (apSlot) {
            0 -> packNormalized(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR)
            1 -> packNormalized(staticIdx, ABSTRACT_MARK, NO_ACCESSOR)
            else -> packNormalized(staticIdx, fieldIdx, ABSTRACT_MARK)
        }
    }

    fun collapse(access: BaseOnlyAccess): BaseOnlyAccess = when (access.apSlot) {
        0 -> packNormalized(NO_ACCESSOR, access.fieldIdx, access.suffixIdx, access.valueAccessorState)
        1 -> packNormalized(access.staticIdx, NO_ACCESSOR, access.suffixIdx, access.valueAccessorState)
        2 -> packNormalized(access.staticIdx, access.fieldIdx, COLLAPSED_MARK)
        else -> access
    }

    fun restoreAbstraction(access: BaseOnlyAccess): BaseOnlyAccess =
        if (access.suffixIdx == COLLAPSED_MARK) packNormalized(access.staticIdx, access.fieldIdx, ABSTRACT_MARK)
        else access

    fun prepend(access: BaseOnlyAccess, idx: AccessorIdx, fieldSensitive: Boolean): BaseOnlyAccess = when {
        idx == TYPE_INFO_GROUP_ACCESSOR_IDX -> {
            require(access.hasTypeInfoSuffix) { "TypeInfoGroupAccessor requires a compact type suffix" }
            access.withValueAccessorState(BaseOnlyValueAccessorState.Value)
        }
        idx.isStaticAccessor() -> {
            require(access.staticIdx == NO_ACCESSOR) { "Cannot prepend a second static accessor" }
            packNormalized(idx, access.fieldIdx, access.suffixIdx, access.valueAccessorState)
        }
        idx.isAnyIdx() -> access
        structural(idx) ->
            if (!fieldSensitive) access
            else packNormalized(access.staticIdx, idx, access.suffixIdx, access.valueAccessorState)
        idx == VALUE_ACCESSOR_IDX -> {
            require(access.hasSemanticMark && access.suffixIdx.isTaintMarkAccessor()) {
                "ValueAccessor requires a taint-mark suffix"
            }
            access.withValueAccessorState(BaseOnlyValueAccessorState.Value)
        }
        else -> packNormalized(access.staticIdx, access.fieldIdx, idx, BaseOnlyValueAccessorState.Normal)
    }

    fun read(access: BaseOnlyAccess, idx: AccessorIdx): BaseOnlyAccess? = when (headRead(access, idx)) {
        HeadRead.NONE -> null
        HeadRead.KEEP -> access
        HeadRead.TAIL -> tail(access)
        HeadRead.WRAPPER_TAIL -> wrapperTail(access)
    }

    fun startsWith(access: BaseOnlyAccess, idx: AccessorIdx): Boolean = headRead(access, idx) != HeadRead.NONE

    fun clear(access: BaseOnlyAccess, idx: AccessorIdx): BaseOnlyAccess? {
        if (access.staticIdx == NO_ACCESSOR && access.fieldIdx == NO_ACCESSOR && access.hasSemanticMark) {
            // The missing field slot includes the implicit Any self-loop. Clearing a terminal
            // root can remove the zero-length branch, but the same terminal remains reachable after
            // one or more structural reads, so the BaseOnly projection is unchanged.
            return access
        }

        val head = access.firstAccessorOrNull ?: return access
        if (head != idx) return access

        return null
    }

    fun append(prefix: BaseOnlyAccess, suffix: BaseOnlyAccess): BaseOnlyAccess? {
        if (suffix.isEmpty) return prefix
        if (prefix.isEmpty) return suffix
        if (prefix.hasAp) return graftAtAbstraction(prefix, suffix)
        if (prefix.hasTerminalAccessor) return prefix
        if (suffix.staticIdx >= 0 && prefix.coreSize > 0) return null
        val prefixStaticConcrete = if (prefix.staticIdx == ABSTRACT_MARK) NO_ACCESSOR else prefix.staticIdx
        val prefixFieldConcrete = if (prefix.fieldIdx == ABSTRACT_MARK) NO_ACCESSOR else prefix.fieldIdx
        val staticIdx = if (suffix.staticIdx >= 0) suffix.staticIdx else prefixStaticConcrete
        val fieldIdx = when {
            prefixFieldConcrete >= 0 -> prefixFieldConcrete
            suffix.fieldIdx != NO_ACCESSOR -> suffix.fieldIdx
            else -> NO_ACCESSOR
        }
        val suffixIdx =
            if (fieldIdx == ABSTRACT_MARK) NO_ACCESSOR
            else combineTerminal(prefix, suffix)
        val valueAccessorState = when {
            prefix.hasSemanticMark -> prefix.valueAccessorState
            suffix.hasSemanticMark -> suffix.valueAccessorState
            else -> BaseOnlyValueAccessorState.Normal
        }
        return packNormalized(staticIdx, fieldIdx, suffixIdx, valueAccessorState)
    }

    fun appendFinal(prefix: BaseOnlyAccess, suffix: BaseOnlyAccess): BaseOnlyAccess? {
        if (suffix.isEmpty) return prefix
        if (!prefix.hasAp) return null
        return graftAtAbstraction(prefix, suffix)
    }

    /**
     * Graft [suffix] at [prefix]'s abstract accepting node. A suffix that starts in a later
     * representational category is valid: loss of an intermediate field is widened with symbolic
     * Any when an exact or semantic terminal follows. Only a second static is structurally
     * impossible.
     */
    private fun graftAtAbstraction(prefix: BaseOnlyAccess, suffix: BaseOnlyAccess): BaseOnlyAccess? {
        return when (prefix.apSlot) {
            0 -> suffix
            1 -> {
                if (suffix.staticIdx != NO_ACCESSOR) return null
                packNormalized(prefix.staticIdx, suffix.fieldIdx, suffix.suffixIdx, suffix.valueAccessorState)
            }
            2 -> {
                if (suffix.staticIdx != NO_ACCESSOR) return null
                // `outer.* + inner.tail` denotes `outer.inner.tail`. BaseOnly retains `outer`,
                // absorbs the unrepresentable inner structural step, and keeps `tail`. Reading
                // `outer` installs the implicit structural self-loop before the terminal, so
                // `outer.tail` covers every concrete `outer.inner.tail` Tree path. Returning
                // `outer.*` here would lose a semantic terminal and underapproximate.
                val field = when {
                    prefix.fieldIdx >= 0 -> prefix.fieldIdx
                    suffix.fieldIdx != NO_ACCESSOR -> suffix.fieldIdx
                    else -> NO_ACCESSOR
                }
                val terminal = when {
                    prefix.fieldIdx >= 0 && suffix.fieldIdx >= 0 && !suffix.hasSemanticMark ->
                        ABSTRACT_MARK
                    suffix.fieldIdx == ABSTRACT_MARK && prefix.fieldIdx >= 0 -> ABSTRACT_MARK
                    else -> suffix.suffixIdx
                }
                packNormalized(prefix.staticIdx, field, terminal, suffix.valueAccessorState)
            }
            else -> null
        }
    }

    private fun slotVal(a: BaseOnlyAccess, slot: Int): AccessorIdx = when (slot) {
        0 -> a.staticIdx
        1 -> a.fieldIdx
        else -> a.suffixIdx
    }

    private fun matchesInitialPrefix(pattern: BaseOnlyAccess, x: BaseOnlyAccess): Boolean {
        if (pattern == x) return true
        if (!pattern.hasAp) return false
        val k = pattern.apSlot
        for (j in 0 until k) {
            val patternSlot = slotVal(pattern, j)
            val factSlot = slotVal(x, j)
            val matches = if (j == 1) fieldCovers(patternSlot, factSlot, pattern) else patternSlot == factSlot
            if (!matches) return false
        }
        if (slotVal(x, k) == NO_ACCESSOR) return false
        if (x.hasAp && x.apSlot < k) return false
        return true
    }

    fun matchPrefix(final: BaseOnlyAccess, initial: BaseOnlyAccess): BaseOnlyMatch {
        if (final == initial) return IDENTITY_MATCH
        if (!matchesInitialPrefix(initial, final)) return NO_MATCH
        return BaseOnlyMatch(emptyDelta = false, hasSuffix = true, suffix = dropCorePrefix(final, initial.apSlot))
    }

    fun splitConcreteInitial(final: BaseOnlyAccess, initial: BaseOnlyAccess): BaseOnlySplit? {
        if (initial.hasAp) return null
        return when (final.apSlot) {
            0 -> BaseOnlySplit(final, initial)
            1 -> {
                if (!staticsCompatible(initial.staticIdx, final.staticIdx)) return null
                BaseOnlySplit(
                    final,
                    packNormalized(NO_ACCESSOR, initial.fieldIdx, initial.suffixIdx, initial.valueAccessorState),
                )
            }
            2 -> {
                if (!staticsCompatible(initial.staticIdx, final.staticIdx)) return null
                if (!fieldsCompatible(initial.fieldIdx, final.fieldIdx)) return null
                BaseOnlySplit(
                    final,
                    packNormalized(NO_ACCESSOR, NO_ACCESSOR, initial.suffixIdx, initial.valueAccessorState),
                )
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

            // A suffix-abstract fact matched by a field-abstract summary still has a suffix
            // beyond the matched field slot. Preserve it so mapping the summary initial and
            // concatenating the delta reconstructs the caller fact. In particular:
            // <field-*> matched against field.* retains field.*; and
            // <field-*> matched against .* retains *.
            if (pattern.apSlot == 1 && fact.apSlot == 2) {
                val delta = dropCorePrefix(fact, pattern.apSlot)
                val filtered = manager.applyExclusions(delta, exclusions) ?: return emptyList()
                return listOf(pattern to BaseOnlyNodeInitialDelta(manager, filtered))
            }

            return listOf(pattern to BaseOnlyEmptyInitialDelta)
        }

        if (pattern.hasAp) {
            val split = splitConcreteInitial(pattern, fact) ?: return emptyList()
            // A field-lenient match may align `knownField.*` with a root-level suffix after
            // projection erased one structural side. The summary exclusion is scoped after the
            // known field and therefore must not be applied to that root-level residual.
            val erasedStructuralBoundary = pattern.apSlot == 2 &&
                ((pattern.fieldIdx == NO_ACCESSOR) != (fact.fieldIdx == NO_ACCESSOR))
            val filtered =
                if (erasedStructuralBoundary) split.delta
                else manager.applyExclusions(split.delta, exclusions) ?: return emptyList()
            return listOf(split.matched to BaseOnlyNodeInitialDelta(manager, filtered))
        }

        if (containsAccess(pattern, fact)) {
            return listOf(pattern to BaseOnlyEmptyInitialDelta)
        }
        return emptyList()
    }

    /** Directional logical coverage: every path in [fact] is represented by [pattern]. */
    fun covers(pattern: BaseOnlyAccess, fact: BaseOnlyAccess): Boolean {
        if (pattern == fact) return true

        if (pattern.staticIdx == ABSTRACT_MARK) return true
        if (fact.staticIdx == ABSTRACT_MARK) return false
        if (!staticsCompatible(pattern.staticIdx, fact.staticIdx)) return false

        if (pattern.fieldIdx == ABSTRACT_MARK) return true
        if (fact.fieldIdx == ABSTRACT_MARK) return false
        if (!fieldCovers(pattern.fieldIdx, fact.fieldIdx, pattern)) return false

        if (pattern.suffixIdx == ABSTRACT_MARK) return true
        if (fact.suffixIdx == ABSTRACT_MARK) return false
        if (pattern.suffixIdx == NO_ACCESSOR) return false
        if (pattern.suffixIdx != fact.suffixIdx) return false
        return !pattern.hasSemanticMark || pattern.valueAccessorState == fact.valueAccessorState
    }

    /** Symmetric candidate relation. It is deliberately distinct from directional [covers]. */
    fun mayOverlap(left: BaseOnlyAccess, right: BaseOnlyAccess): Boolean {
        if (left == right) return true
        if (left.staticIdx == ABSTRACT_MARK || right.staticIdx == ABSTRACT_MARK) return true
        if (!staticsCompatible(left.staticIdx, right.staticIdx)) return false

        if (left.fieldIdx == ABSTRACT_MARK || right.fieldIdx == ABSTRACT_MARK) return true
        if (left.fieldIdx >= 0 && right.fieldIdx >= 0 && left.fieldIdx != right.fieldIdx) return false
        if (left.fieldIdx >= 0 && right.fieldIdx == NO_ACCESSOR && !hasVirtualStructuralAny(right)
        ) return false
        if (right.fieldIdx >= 0 && left.fieldIdx == NO_ACCESSOR && !hasVirtualStructuralAny(left)
        ) return false

        if (left.suffixIdx == ABSTRACT_MARK || right.suffixIdx == ABSTRACT_MARK) return true
        if (left.suffixIdx == NO_ACCESSOR || right.suffixIdx == NO_ACCESSOR) return false
        if (left.suffixIdx != right.suffixIdx) return false
        return !left.hasSemanticMark || left.valueAccessorState == right.valueAccessorState
    }

    /**
     * Projected final-to-initial containment.
     *
     * A missing structural slot is compatible with a concrete structural slot here because
     * BaseOnly projection erases intermediate fields. This relation is intentionally broader
     * than directional [covers]: it implements the cross-domain `FinalFactAp.contains`
     * contract, not storage subsumption.
     */
    fun containsAccess(final: BaseOnlyAccess, initial: BaseOnlyAccess): Boolean {
        if (final == initial) return true

        if (final.staticIdx == ABSTRACT_MARK) return true
        if (!staticsCompatible(final.staticIdx, initial.staticIdx)) return false

        if (final.fieldIdx == ABSTRACT_MARK) return true
        if (!fieldsCompatible(final.fieldIdx, initial.fieldIdx)) return false

        if (final.suffixIdx == ABSTRACT_MARK) return true
        if (final.suffixIdx == NO_ACCESSOR) return false
        if (final.suffixIdx != initial.suffixIdx) return false
        return !final.hasSemanticMark || final.valueAccessorState == initial.valueAccessorState
    }

    fun equalToInitial(final: BaseOnlyAccess, initial: BaseOnlyAccess): Boolean {
        if (initial.staticIdx != final.staticIdx) return false
        if (initial.fieldIdx != final.fieldIdx) return false
        val initialSemantic = if (initial.hasSemanticMark) initial.suffixIdx else NO_ACCESSOR
        val finalSemantic = if (final.hasSemanticMark) final.suffixIdx else NO_ACCESSOR
        if (initialSemantic != finalSemantic) return false
        if (initialSemantic >= 0 && initial.valueAccessorState != final.valueAccessorState) return false
        val terminalsAgree =
            if (initial.hasTerminalAccessor) !final.isSuffixAbstract
            else final.isSuffixAbstract == initial.isSuffixAbstract
        return terminalsAgree
    }

    private enum class HeadRead { NONE, KEEP, TAIL, WRAPPER_TAIL }

    private fun headRead(access: BaseOnlyAccess, idx: AccessorIdx): HeadRead {
        if (access.staticIdx >= 0) return if (idx == access.staticIdx) HeadRead.TAIL else HeadRead.NONE
        if (access.staticIdx == ABSTRACT_MARK) return HeadRead.NONE
        if (access.fieldIdx >= 0) return if (idx == access.fieldIdx) HeadRead.TAIL else HeadRead.NONE
        if (access.fieldIdx == ABSTRACT_MARK) return HeadRead.NONE
        return when {
            access.hasSemanticMark -> when {
                structural(idx) -> HeadRead.KEEP
                idx == terminalWrapperIdx(access) && access.valueAccessorState == BaseOnlyValueAccessorState.Value ->
                    HeadRead.WRAPPER_TAIL
                idx == access.suffixIdx && access.valueAccessorState == BaseOnlyValueAccessorState.Normal -> HeadRead.TAIL
                else -> HeadRead.NONE
            }
            access.suffixIdx == ABSTRACT_MARK -> if (structural(idx)) HeadRead.KEEP else HeadRead.NONE
            access.isCollapsed -> if (structural(idx)) HeadRead.KEEP else HeadRead.NONE
            access.suffixIdx == FINAL_ACCESSOR_IDX -> if (idx == FINAL_ACCESSOR_IDX) HeadRead.KEEP else HeadRead.NONE
            else -> HeadRead.NONE
        }
    }

    private fun tail(access: BaseOnlyAccess): BaseOnlyAccess = when {
        access.staticIdx >= 0 -> packNormalized(
            NO_ACCESSOR, access.fieldIdx, access.suffixIdx, access.valueAccessorState
        )
        access.fieldIdx >= 0 ->
            packNormalized(NO_ACCESSOR, NO_ACCESSOR, access.suffixIdx, access.valueAccessorState)
        access.hasSemanticMark -> packNormalized(NO_ACCESSOR, NO_ACCESSOR, FINAL_ACCESSOR_IDX)
        else -> EMPTY_ACCESS
    }

    private fun wrapperTail(access: BaseOnlyAccess): BaseOnlyAccess =
        packNormalized(NO_ACCESSOR, NO_ACCESSOR, access.suffixIdx, BaseOnlyValueAccessorState.Normal)

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
        return packNormalized(staticIdx, fieldIdx, access.suffixIdx, access.valueAccessorState)
    }

    private fun structural(idx: AccessorIdx): Boolean = idx.isStructuralIdx() || idx.isAnyIdx()

    private fun terminalWrapperIdx(access: BaseOnlyAccess): AccessorIdx = when {
        access.hasTypeInfoSuffix -> TYPE_INFO_GROUP_ACCESSOR_IDX
        access.suffixIdx.isTaintMarkAccessor() -> VALUE_ACCESSOR_IDX
        else -> NO_ACCESSOR
    }

    private fun hasVirtualStructuralAny(access: BaseOnlyAccess): Boolean =
        access.fieldIdx == NO_ACCESSOR &&
            (access.hasSemanticMark || access.isSuffixAbstract || access.isCollapsed)

    private fun fieldCovers(patternField: AccessorIdx, factField: AccessorIdx, pattern: BaseOnlyAccess): Boolean = when {
        patternField == factField -> true
        patternField == NO_ACCESSOR -> factField >= 0 && hasVirtualStructuralAny(pattern)
        else -> false
    }

    private fun staticsCompatible(a: AccessorIdx, b: AccessorIdx): Boolean = a == b

    private fun fieldsCompatible(a: AccessorIdx, b: AccessorIdx): Boolean =
        a == NO_ACCESSOR || b == NO_ACCESSOR || a == b

    private fun packNormalized(
        staticIdx: AccessorIdx,
        fieldIdx: AccessorIdx,
        suffixIdx: AccessorIdx,
        valueAccessorState: BaseOnlyValueAccessorState = BaseOnlyValueAccessorState.Normal,
    ): BaseOnlyAccess {
        val apEarlier = staticIdx == ABSTRACT_MARK || fieldIdx == ABSTRACT_MARK
        val normalizedSuffix =
            if (suffixIdx == NO_ACCESSOR && !apEarlier && (staticIdx >= 0 || fieldIdx >= 0)) ABSTRACT_MARK
            else suffixIdx
        val normalizedState =
            if (normalizedSuffix >= 0 && normalizedSuffix != FINAL_ACCESSOR_IDX) valueAccessorState
            else BaseOnlyValueAccessorState.Normal
        return packBaseOnlyAccess(staticIdx, fieldIdx, normalizedSuffix, normalizedState)
    }

    private val NO_MATCH = BaseOnlyMatch(emptyDelta = false, hasSuffix = false, suffix = EMPTY_ACCESS)
    private val IDENTITY_MATCH = BaseOnlyMatch(emptyDelta = true, hasSuffix = false, suffix = EMPTY_ACCESS)
}
