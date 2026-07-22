package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTypeInfoAccessor

typealias BaseOnlyAccess = Long

const val NO_ACCESSOR: AccessorIdx = -1
const val ABSTRACT_MARK: AccessorIdx = -2
const val COLLAPSED_MARK: AccessorIdx = -3

const val BASE_ONLY_STATIC_BITS = 16
const val BASE_ONLY_FIELD_BITS = 24
const val BASE_ONLY_SUFFIX_BITS = 24
const val BASE_ONLY_VALUE_ACCESSOR_STATE_BITS = 1
const val BASE_ONLY_SUFFIX_VALUE_BITS = BASE_ONLY_SUFFIX_BITS - BASE_ONLY_VALUE_ACCESSOR_STATE_BITS

const val BASE_ONLY_SUFFIX_SHIFT = 0
const val BASE_ONLY_FIELD_SHIFT = BASE_ONLY_SUFFIX_BITS
const val BASE_ONLY_STATIC_SHIFT = BASE_ONLY_SUFFIX_BITS + BASE_ONLY_FIELD_BITS

const val BASE_ONLY_STATIC_MASK = (1 shl BASE_ONLY_STATIC_BITS) - 1
const val BASE_ONLY_FIELD_MASK = (1 shl BASE_ONLY_FIELD_BITS) - 1
const val BASE_ONLY_SUFFIX_MASK = (1 shl BASE_ONLY_SUFFIX_BITS) - 1
const val BASE_ONLY_SUFFIX_VALUE_MASK = (1 shl BASE_ONLY_SUFFIX_VALUE_BITS) - 1
const val BASE_ONLY_VALUE_ACCESSOR_STATE_SHIFT = BASE_ONLY_SUFFIX_VALUE_BITS
const val BASE_ONLY_VALUE_ACCESSOR_STATE_MASK = (1 shl BASE_ONLY_VALUE_ACCESSOR_STATE_BITS) - 1

const val BASE_ONLY_BIAS = 3

/**
 * How the semantic suffix is reached. [Value] encodes a preceding ValueAccessor;
 * for a type suffix the same bit encodes its analogous TypeInfoGroupAccessor prefix.
 */
enum class BaseOnlyValueAccessorState(val encoded: Int) {
    Normal(0),
    Value(1);

    companion object {
        fun decode(encoded: Int): BaseOnlyValueAccessorState =
            entries.firstOrNull { it.encoded == encoded }
                ?: throw IllegalArgumentException("Invalid BaseOnly value-accessor state: $encoded")
    }
}

fun packBaseOnlyAccess(
    staticIdx: AccessorIdx,
    fieldIdx: AccessorIdx,
    suffixIdx: AccessorIdx,
    valueAccessorState: BaseOnlyValueAccessorState = BaseOnlyValueAccessorState.Normal,
): BaseOnlyAccess {
    require(fieldIdx != ANY_ACCESSOR_IDX) { "AnyAccessor is implicit in BaseOnly and cannot occupy the field slot" }
    val s = staticIdx + BASE_ONLY_BIAS
    val f = fieldIdx + BASE_ONLY_BIAS
    val x = suffixIdx + BASE_ONLY_BIAS
    require(s in 0..BASE_ONLY_STATIC_MASK) { "BaseOnly static index out of range: $staticIdx" }
    require(f in 0..BASE_ONLY_FIELD_MASK) { "BaseOnly field index out of range: $fieldIdx" }
    require(x in 0..BASE_ONLY_SUFFIX_VALUE_MASK) { "BaseOnly suffix index out of range: $suffixIdx" }
    val encodedSuffix = rawBaseOnlySuffixSlot(suffixIdx, valueAccessorState)
    return (s.toLong() shl BASE_ONLY_STATIC_SHIFT) or
        (f.toLong() shl BASE_ONLY_FIELD_SHIFT) or encodedSuffix.toLong()
}

fun rawBaseOnlySuffixSlot(suffixIdx: AccessorIdx, valueAccessorState: BaseOnlyValueAccessorState): Int {
    val encodedSuffix = suffixIdx + BASE_ONLY_BIAS
    require(encodedSuffix in 0..BASE_ONLY_SUFFIX_VALUE_MASK) {
        "BaseOnly suffix index out of range: $suffixIdx"
    }
    return encodedSuffix or (valueAccessorState.encoded shl BASE_ONLY_VALUE_ACCESSOR_STATE_SHIFT)
}

fun packBaseOnlyAccessFromRawSuffix(
    staticIdx: AccessorIdx,
    fieldIdx: AccessorIdx,
    rawSuffixSlot: Int,
): BaseOnlyAccess {
    val suffixIdx = (rawSuffixSlot and BASE_ONLY_SUFFIX_VALUE_MASK) - BASE_ONLY_BIAS
    val state = BaseOnlyValueAccessorState.decode(
        (rawSuffixSlot ushr BASE_ONLY_VALUE_ACCESSOR_STATE_SHIFT) and BASE_ONLY_VALUE_ACCESSOR_STATE_MASK
    )
    return packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx, state)
}

val EMPTY_ACCESS: BaseOnlyAccess = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, NO_ACCESSOR)
val ABSTRACT_EMPTY_ACCESS: BaseOnlyAccess = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, ABSTRACT_MARK)
val FINAL_ACCESS: BaseOnlyAccess = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, FINAL_ACCESSOR_IDX)

inline fun <T> BaseOnlyAccess.withBaseOnlyAccessUnpacked(
    body: (staticIdx: AccessorIdx, fieldIdx: AccessorIdx, suffixIdx: AccessorIdx) -> T,
): T = body(
    ((this ushr BASE_ONLY_STATIC_SHIFT).toInt() and BASE_ONLY_STATIC_MASK) - BASE_ONLY_BIAS,
    ((this ushr BASE_ONLY_FIELD_SHIFT).toInt() and BASE_ONLY_FIELD_MASK) - BASE_ONLY_BIAS,
    (this.toInt() and BASE_ONLY_SUFFIX_VALUE_MASK) - BASE_ONLY_BIAS,
)

val BaseOnlyAccess.staticIdx: AccessorIdx
    get() = ((this ushr BASE_ONLY_STATIC_SHIFT).toInt() and BASE_ONLY_STATIC_MASK) - BASE_ONLY_BIAS

val BaseOnlyAccess.fieldIdx: AccessorIdx
    get() = ((this ushr BASE_ONLY_FIELD_SHIFT).toInt() and BASE_ONLY_FIELD_MASK) - BASE_ONLY_BIAS

val BaseOnlyAccess.suffixIdx: AccessorIdx
    get() = (this.toInt() and BASE_ONLY_SUFFIX_VALUE_MASK) - BASE_ONLY_BIAS

val BaseOnlyAccess.rawSuffixSlot: Int
    get() = this.toInt() and BASE_ONLY_SUFFIX_MASK

val BaseOnlyAccess.valueAccessorState: BaseOnlyValueAccessorState
    get() = BaseOnlyValueAccessorState.decode(
        (rawSuffixSlot ushr BASE_ONLY_VALUE_ACCESSOR_STATE_SHIFT) and BASE_ONLY_VALUE_ACCESSOR_STATE_MASK
    )

fun BaseOnlyAccess.withValueAccessorState(state: BaseOnlyValueAccessorState): BaseOnlyAccess =
    packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx, state)

val BaseOnlyAccess.isSuffixAbstract: Boolean get() = suffixIdx == ABSTRACT_MARK

val BaseOnlyAccess.isCollapsed: Boolean get() = suffixIdx == COLLAPSED_MARK

val BaseOnlyAccess.apSlot: Int
    get() = withBaseOnlyAccessUnpacked { s, f, x ->
        when {
            s == ABSTRACT_MARK -> 0
            f == ABSTRACT_MARK -> 1
            x == ABSTRACT_MARK -> 2
            else -> -1
        }
    }

val BaseOnlyAccess.hasAp: Boolean get() = apSlot >= 0

val BaseOnlyAccess.hasSemanticMark: Boolean get() = suffixIdx >= 0 && suffixIdx != FINAL_ACCESSOR_IDX

val BaseOnlyAccess.hasTerminalAccessor: Boolean get() = suffixIdx >= 0

val BaseOnlyAccess.hasTypeInfoSuffix: Boolean get() = suffixIdx >= 0 && suffixIdx.isTypeInfoAccessor()

val BaseOnlyAccess.size: Int
    get() = withBaseOnlyAccessUnpacked { staticIdx, fieldIdx, suffixIdx ->
        var result = 0
        if (staticIdx >= 0) result++
        if (fieldIdx >= 0) result++
        if (suffixIdx >= 0) result++
        result
    }

val BaseOnlyAccess.coreSize: Int
    get() = withBaseOnlyAccessUnpacked { s, f, x ->
        var n = 0
        if (s >= 0) n++
        if (f >= 0) n++
        if (x >= 0 && x != FINAL_ACCESSOR_IDX) n++
        n
    }

val BaseOnlyAccess.isEmpty: Boolean get() = this == EMPTY_ACCESS

val BaseOnlyAccess.headOrNull: AccessorIdx?
    get() = withBaseOnlyAccessUnpacked { s, f, x ->
        when {
            s >= 0 -> s
            f >= 0 -> f
            x >= 0 && x != FINAL_ACCESSOR_IDX -> x
            x == FINAL_ACCESSOR_IDX -> FINAL_ACCESSOR_IDX
            else -> null
        }
    }

val BaseOnlyAccess.firstAccessorOrNull: AccessorIdx?
    get() = withBaseOnlyAccessUnpacked { s, f, x ->
        when {
            s >= 0 -> s
            f >= 0 -> f
            x < 0 -> null
            x == FINAL_ACCESSOR_IDX -> FINAL_ACCESSOR_IDX
            x.isTypeInfoAccessor() && valueAccessorState == BaseOnlyValueAccessorState.Value -> TYPE_INFO_GROUP_ACCESSOR_IDX
            else -> x
        }
    }

fun BaseOnlyAccess.coreAt(position: Int): AccessorIdx = withBaseOnlyAccessUnpacked { s, f, x ->
    var k = position
    if (s >= 0) { if (k == 0) return@withBaseOnlyAccessUnpacked s; k-- }
    if (f >= 0) { if (k == 0) return@withBaseOnlyAccessUnpacked f; k-- }
    if (x >= 0 && x != FINAL_ACCESSOR_IDX) { if (k == 0) return@withBaseOnlyAccessUnpacked x; k-- }
    NO_ACCESSOR
}

fun BaseOnlyAccess.coreStartsWith(prefix: BaseOnlyAccess, prefixLen: Int): Boolean {
    if (coreSize < prefixLen) return false
    for (i in 0 until prefixLen) if (coreAt(i) != prefix.coreAt(i)) return false
    return true
}

inline fun BaseOnlyAccess.forEachAccessorIdx(action: (AccessorIdx) -> Unit) {
    val s = staticIdx
    val f = fieldIdx
    val x = suffixIdx
    if (s >= 0) action(s)
    if (f >= 0) action(f)
    if (x >= 0) {
        if (x != FINAL_ACCESSOR_IDX) {
            if (x.isTypeInfoAccessor() && valueAccessorState == BaseOnlyValueAccessorState.Value) {
                action(TYPE_INFO_GROUP_ACCESSOR_IDX)
            }
            action(x)
        }
        action(FINAL_ACCESSOR_IDX)
    }
}

inline fun BaseOnlyAccess.forEachCoreIdx(action: (AccessorIdx) -> Unit) {
    val s = staticIdx
    val f = fieldIdx
    val x = suffixIdx
    if (s >= 0) action(s)
    if (f >= 0) action(f)
    if (x >= 0 && x != FINAL_ACCESSOR_IDX) action(x)
}

fun AccessorIdx.isAnyIdx(): Boolean = this == ANY_ACCESSOR_IDX
fun AccessorIdx.isStructuralIdx(): Boolean = isFieldAccessor() || this == ELEMENT_ACCESSOR_IDX
fun AccessorIdx.isSuffixIdx(): Boolean = !isAnyIdx() && !isStructuralIdx() && !isStaticAccessor()

class BaseOnlyMatch(
    @JvmField val emptyDelta: Boolean,
    @JvmField val hasSuffix: Boolean,
    @JvmField val suffix: BaseOnlyAccess,
)
