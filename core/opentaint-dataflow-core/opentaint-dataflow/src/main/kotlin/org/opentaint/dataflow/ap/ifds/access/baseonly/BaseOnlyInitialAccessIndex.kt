package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.util.ConcurrentReadSafeInt2ObjectMap
import org.opentaint.dataflow.util.forEachEntry
import org.opentaint.dataflow.util.getOrCreateNullable
import org.opentaint.dataflow.util.int2ObjectMap

/**
 * A single-writer/multiple-reader index over the three packed BaseOnly access slots.
 *
 * Patterned traversal is deliberately conservative and returns candidates only. Callers apply
 * the semantic predicate of their operation before emission.
 */
internal class BaseOnlyInitialAccessIndex<V : Any> {
    private class FieldNode<V : Any> {
        val fields: ConcurrentReadSafeInt2ObjectMap<SuffixNode<V>?> = int2ObjectMap()
    }

    private class SuffixNode<V : Any> {
        val suffixes: ConcurrentReadSafeInt2ObjectMap<V?> = int2ObjectMap()
    }

    private val statics: ConcurrentReadSafeInt2ObjectMap<FieldNode<V>?> = int2ObjectMap()

    fun getOrCreate(access: BaseOnlyAccess, create: () -> V): V {
        val fieldNode = statics.getOrCreateNullable(access.staticIdx) { FieldNode() }
        val suffixNode = fieldNode.fields.getOrCreateNullable(access.fieldIdx) { SuffixNode() }
        return suffixNode.suffixes.getOrCreateNullable(access.rawSuffixSlot, create)
    }

    fun get(access: BaseOnlyAccess): V? =
        statics.get(access.staticIdx)
            ?.fields?.get(access.fieldIdx)
            ?.suffixes?.get(access.rawSuffixSlot)

    fun collectAll(consume: (BaseOnlyAccess, V) -> Unit) {
        statics.forEachEntry { staticIdx, fieldNode ->
            fieldNode?.collectAll(staticIdx, consume)
        }
    }

    fun collectCandidates(pattern: BaseOnlyAccess, consume: (BaseOnlyAccess, V) -> Unit) {
        if (pattern.staticIdx == ABSTRACT_MARK) {
            collectAll(consume)
            return
        }

        statics.get(ABSTRACT_MARK)?.collectAll(ABSTRACT_MARK, consume)
        val fieldNode = statics.get(pattern.staticIdx) ?: return
        if (pattern.fieldIdx == ABSTRACT_MARK) {
            fieldNode.collectAll(pattern.staticIdx, consume)
            return
        }

        fieldNode.fields.get(ABSTRACT_MARK)?.collectAll(pattern.staticIdx, ABSTRACT_MARK, consume)
        when (pattern.fieldIdx) {
            NO_ACCESSOR -> fieldNode.fields.forEachEntry { fieldIdx, suffixNode ->
                suffixNode?.collectCandidates(pattern.staticIdx, fieldIdx, pattern, consume)
            }

            else -> {
                fieldNode.fields.get(pattern.fieldIdx)?.collectCandidates(
                    pattern.staticIdx,
                    pattern.fieldIdx,
                    pattern,
                    consume,
                )
                fieldNode.fields.get(NO_ACCESSOR)?.collectCandidates(
                    pattern.staticIdx,
                    NO_ACCESSOR,
                    pattern,
                    consume,
                )
            }
        }
    }

    private fun FieldNode<V>.collectAll(staticIdx: Int, consume: (BaseOnlyAccess, V) -> Unit) {
        fields.forEachEntry { fieldIdx, suffixNode ->
            suffixNode?.collectAll(staticIdx, fieldIdx, consume)
        }
    }

    private fun SuffixNode<V>.collectCandidates(
        staticIdx: Int,
        fieldIdx: Int,
        pattern: BaseOnlyAccess,
        consume: (BaseOnlyAccess, V) -> Unit,
    ) {
        if (pattern.suffixIdx == ABSTRACT_MARK) {
            collectAll(staticIdx, fieldIdx, consume)
            return
        }

        val abstractSuffix = rawBaseOnlySuffixSlot(ABSTRACT_MARK, BaseOnlyValueAccessorState.Normal)
        suffixes.get(abstractSuffix)?.let { value ->
            consume(packBaseOnlyAccessFromRawSuffix(staticIdx, fieldIdx, abstractSuffix), value)
        }

        val states =
            if (pattern.hasSemanticMark) BaseOnlyValueAccessorState.entries
            else listOf(BaseOnlyValueAccessorState.Normal)
        for (state in states) {
            val rawSuffix = rawBaseOnlySuffixSlot(pattern.suffixIdx, state)
            suffixes.get(rawSuffix)?.let { value ->
                consume(packBaseOnlyAccessFromRawSuffix(staticIdx, fieldIdx, rawSuffix), value)
            }
        }
    }

    private fun SuffixNode<V>.collectAll(
        staticIdx: Int,
        fieldIdx: Int,
        consume: (BaseOnlyAccess, V) -> Unit,
    ) {
        suffixes.forEachEntry { rawSuffix, value ->
            value?.let { consume(packBaseOnlyAccessFromRawSuffix(staticIdx, fieldIdx, rawSuffix), it) }
        }
    }

}

/** Tree's filterContains is a symmetric applicability query, not directional containment. */
internal fun baseOnlySummaryInitialMatches(pattern: BaseOnlyAccess, initial: BaseOnlyAccess): Boolean =
    BaseOnlyAccessOps.mayOverlap(pattern, initial)
