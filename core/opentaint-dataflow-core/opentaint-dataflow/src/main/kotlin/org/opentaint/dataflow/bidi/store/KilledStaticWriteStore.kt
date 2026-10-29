package org.opentaint.dataflow.bidi.store

import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntLinkedOpenHashSet
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap
import it.unimi.dsi.fastutil.longs.LongArrayList
import org.opentaint.dataflow.bidi.ap.*
import java.util.Collections

/** Raw scalar data for ordinary actual-call binding. This is not an executable summary. */
data class StaticWriteKey(val original: InitialAp, val result: Pattern) {
    fun guidance(): StaticGuidanceEdge {
        val (from, to) = normalizeFlowSummaryPatterns(original.toPattern(), result)
        return StaticGuidanceEdge.of(from, to)
    }
}

private data class StaticWriteGeometry(val original: Pattern, val result: Pattern)

/** Share geometry once and pack the exact input/output mark pair in one primitive word.
 * Unlike the B-only interner, this directory also represents ordinary and genuine ZERO inputs.
 * FLOW output mark exclusions remain raw until actual-call application has finished. */
class StaticWriteKeyInterner(private val ap: ApManager) {
    private val geometryIds = HashMap<StaticWriteGeometry, Int>()
    private val geometries = ArrayList<StaticWriteGeometry>()
    private val labels = ArrayList<Long2IntOpenHashMap>()
    private val rowGeometry = IntArrayList()
    private val rowMarks = LongArrayList()

    @Synchronized fun intern(original: InitialAp, result: Pattern): Int {
        ap.cancellation.checkpoint()
        check(original.manager === ap) { "A static-write key must use its owner's AP manager" }
        check(result.fact.base == STATIC) { "A static-write key needs a static image" }
        check((original.mark is MarkSlot.Star) == (result.fact.mark is MarkSlot.Star)) {
            "A static-write key preserves the original's FLOW/TAINT relation"
        }
        fun geometry(pattern: Pattern): Pattern = pattern.copy(fact = pattern.fact.copy(
            path = Collections.unmodifiableList(ArrayList(pattern.fact.path)),
            mark = if (pattern.fact.mark is MarkSlot.Concrete) MarkSlot.STAR else pattern.fact.mark))
        val shape = StaticWriteGeometry(geometry(original.toPattern()), geometry(result))
        val shapeId = geometryIds.getOrPut(shape) {
            geometries.size.also {
                geometries += shape
                labels += Long2IntOpenHashMap().apply { defaultReturnValue(-1) }
            }
        }
        val input = original.mark
        val output = result.fact.mark
        val pair = if (input is MarkSlot.Concrete && output is MarkSlot.Concrete)
            ((input.mark.id.toLong() + 1L) shl 32) or ((output.mark.id.toLong() + 1L) and 0xffffffffL)
        else 0L
        val existing = labels[shapeId].get(pair)
        if (existing >= 0) return existing
        val id = rowGeometry.size
        rowGeometry.add(shapeId)
        rowMarks.add(pair)
        labels[shapeId].put(pair, id)
        return id
    }

    @Synchronized fun row(id: Int): StaticWriteKey {
        ap.cancellation.checkpoint()
        val shape = geometries[rowGeometry.getInt(id)]
        val pair = rowMarks.getLong(id)
        val original = if (pair == 0L) shape.original else shape.original.copy(fact = shape.original.fact.copy(
            mark = MarkSlot.Concrete(TaintMark((pair ushr 32).toInt() - 1))))
        val result = if (pair == 0L) shape.result else shape.result.copy(fact = shape.result.fact.copy(
            mark = MarkSlot.Concrete(TaintMark(pair.toInt() - 1))))
        return StaticWriteKey(ap.initial(original), result)
    }

    @Synchronized fun clear() {
        geometryIds.clear(); geometries.clear(); labels.clear(); rowGeometry.clear(); rowMarks.clear()
    }
}

/** Borrow only before the shared key directory is released at run-1 handoff. */
class FrozenStaticWrites internal constructor(
    val owner: MethodKey,
    val interner: StaticWriteKeyInterner,
    private val observed: IntArray,
    private val lost: IntArray,
    val peakCount: Int,
) {
    val observedCount: Int get() = observed.size
    val lostCount: Int get() = lost.size
    fun observedIds(): IntArray = observed.copyOf()
    fun lostIds(): IntArray = lost.copyOf()
    fun forEachObservedId(visit: (Int) -> Unit) { for (id in observed) visit(id) }
    fun forEachLostId(visit: (Int) -> Unit) { for (id in lost) visit(id) }
    fun observedRows(): Sequence<StaticWriteKey> = observed.asSequence().map(interner::row)
    fun lostRows(): Sequence<StaticWriteKey> = lost.asSequence().map(interner::row)
}

/** Actor-owned candidates, not a killed-only set. Keep every observed thin ID until the
 * joined final prune: FLOW-backed common storage can later erase a colored survivor. */
class KilledStaticWriteStore(
    private val owner: MethodKey,
    private val ap: ApManager,
    private val ops: ApOps,
    private val interner: StaticWriteKeyInterner,
) {
    private var candidates: IntLinkedOpenHashSet? = IntLinkedOpenHashSet()
    private var frozen: FrozenStaticWrites? = null
    val candidateCount: Int get() = frozen?.observedCount ?: checkNotNull(candidates).size
    var peakCount: Int = 0; private set

    fun observe(original: PremiseKey, result: Facts) {
        check(frozen == null) { "A completed static-write inventory cannot accept new observations" }
        ap.cancellation.checkpoint()
        check(original is InitialAp) { "Run-1 static-write candidates have one original" }
        if (result.base != STATIC) return
        val pending = checkNotNull(candidates)
        for (leaf in ops.leaves(result)) {
            ap.cancellation.checkpoint()
            pending.add(interner.intern(original, leaf))
        }
        peakCount = maxOf(peakCount, pending.size)
    }

    /** Read current survivor views only at joined quiescence. Guidance normalization is
     * for equality here; observed rows retain their raw AP data for caller binding. */
    fun freeze(
        common: Sequence<Pair<PremiseKey, Facts>>,
        privateB: Sequence<StaticGuidanceEdge>,
    ): FrozenStaticWrites {
        frozen?.let { return it }
        val survivors = HashSet<StaticGuidanceEdge>()
        for ((original, result) in common) {
            ap.cancellation.checkpoint()
            check(original is InitialAp) { "Run-1 summaries have one original" }
            if (result.base != STATIC) continue
            for (leaf in ops.leaves(result)) {
                ap.cancellation.checkpoint()
                val (from, to) = normalizeFlowSummaryPatterns(original.toPattern(), leaf)
                survivors += StaticGuidanceEdge.of(from, to)
            }
        }
        for (row in privateB) {
            ap.cancellation.checkpoint()
            val (from, to) = normalizeFlowSummaryPatterns(row.from, row.to)
            survivors += StaticGuidanceEdge.of(from, to)
        }
        val observed = checkNotNull(candidates).toIntArray()
        val lost = IntArrayList()
        for (id in observed) {
            ap.cancellation.checkpoint()
            if (interner.row(id).guidance() !in survivors) lost.add(id)
        }
        return FrozenStaticWrites(owner, interner, observed, lost.toIntArray(), peakCount).also {
            frozen = it
            candidates = null // Release the mutable hash table, including its backing arrays.
        }
    }
}
