package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.util.ConcurrentReadSafeInt2ObjectMap
import org.opentaint.dataflow.util.forEachEntry
import org.opentaint.dataflow.util.getOrCreateNullable
import org.opentaint.dataflow.util.int2ObjectMap

/**
 * A single-writer/multiple-reader index over the three packed BaseOnly access slots.
 *
 * Patterned traversal is deliberately conservative. [baseOnlySummaryInitialMatches] remains the
 * authoritative predicate before a candidate is emitted.
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
        return suffixNode.suffixes.getOrCreateNullable(access.suffixIdx, create)
    }

    fun collectAll(consume: (BaseOnlyAccess, V) -> Unit) {
        statics.forEachEntry { staticIdx, fieldNode ->
            fieldNode?.collectAll(staticIdx, consume)
        }
    }

    fun collectContainedBy(pattern: BaseOnlyAccess, consume: (BaseOnlyAccess, V) -> Unit) {
        if (pattern.staticIdx == ABSTRACT_MARK) {
            collectAllChecked(pattern, consume)
            return
        }

        statics.get(ABSTRACT_MARK)?.collectAllChecked(ABSTRACT_MARK, pattern, consume)
        val fieldNode = statics.get(pattern.staticIdx) ?: return
        if (pattern.fieldIdx == ABSTRACT_MARK) {
            fieldNode.collectAllChecked(pattern.staticIdx, pattern, consume)
            return
        }

        fieldNode.fields.get(ABSTRACT_MARK)?.collectAllChecked(
            pattern.staticIdx,
            ABSTRACT_MARK,
            pattern,
            consume,
        )
        when (pattern.fieldIdx) {
            NO_ACCESSOR -> fieldNode.fields.forEachEntry { fieldIdx, suffixNode ->
                suffixNode?.collectContainedBy(pattern.staticIdx, fieldIdx, pattern, consume)
            }

            else -> {
                fieldNode.fields.get(pattern.fieldIdx)?.collectContainedBy(
                    pattern.staticIdx,
                    pattern.fieldIdx,
                    pattern,
                    consume,
                )
                fieldNode.fields.get(NO_ACCESSOR)?.collectContainedBy(
                    pattern.staticIdx,
                    NO_ACCESSOR,
                    pattern,
                    consume,
                )
            }
        }
    }

    private fun collectAllChecked(pattern: BaseOnlyAccess, consume: (BaseOnlyAccess, V) -> Unit) {
        collectAll { access, value ->
            if (baseOnlySummaryInitialMatches(pattern, access)) consume(access, value)
        }
    }

    private fun FieldNode<V>.collectAll(staticIdx: Int, consume: (BaseOnlyAccess, V) -> Unit) {
        fields.forEachEntry { fieldIdx, suffixNode ->
            suffixNode?.collectAll(staticIdx, fieldIdx, consume)
        }
    }

    private fun FieldNode<V>.collectAllChecked(
        staticIdx: Int,
        pattern: BaseOnlyAccess,
        consume: (BaseOnlyAccess, V) -> Unit,
    ) {
        fields.forEachEntry { fieldIdx, suffixNode ->
            suffixNode?.collectAllChecked(staticIdx, fieldIdx, pattern, consume)
        }
    }

    private fun SuffixNode<V>.collectContainedBy(
        staticIdx: Int,
        fieldIdx: Int,
        pattern: BaseOnlyAccess,
        consume: (BaseOnlyAccess, V) -> Unit,
    ) {
        if (pattern.suffixIdx == ABSTRACT_MARK) {
            collectAllChecked(staticIdx, fieldIdx, pattern, consume)
            return
        }

        suffixes.get(ABSTRACT_MARK)?.let { value ->
            emitIfContained(staticIdx, fieldIdx, ABSTRACT_MARK, value, pattern, consume)
        }
        suffixes.get(pattern.suffixIdx)?.let { value ->
            emitIfContained(staticIdx, fieldIdx, pattern.suffixIdx, value, pattern, consume)
        }
    }

    private fun SuffixNode<V>.collectAll(
        staticIdx: Int,
        fieldIdx: Int,
        consume: (BaseOnlyAccess, V) -> Unit,
    ) {
        suffixes.forEachEntry { suffixIdx, value ->
            value?.let { consume(packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx), it) }
        }
    }

    private fun SuffixNode<V>.collectAllChecked(
        staticIdx: Int,
        fieldIdx: Int,
        pattern: BaseOnlyAccess,
        consume: (BaseOnlyAccess, V) -> Unit,
    ) {
        suffixes.forEachEntry { suffixIdx, value ->
            value?.let { emitIfContained(staticIdx, fieldIdx, suffixIdx, it, pattern, consume) }
        }
    }

    private fun emitIfContained(
        staticIdx: Int,
        fieldIdx: Int,
        suffixIdx: Int,
        value: V,
        pattern: BaseOnlyAccess,
        consume: (BaseOnlyAccess, V) -> Unit,
    ) {
        val access = packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx)
        if (baseOnlySummaryInitialMatches(pattern, access)) consume(access, value)
    }
}

/** Tree's filterContains returns both stored prefixes and descendants of an abstract pattern. */
internal fun baseOnlySummaryInitialMatches(pattern: BaseOnlyAccess, initial: BaseOnlyAccess): Boolean =
    BaseOnlyAccessOps.containsAccess(pattern, initial) || BaseOnlyAccessOps.containsAccess(initial, pattern)
