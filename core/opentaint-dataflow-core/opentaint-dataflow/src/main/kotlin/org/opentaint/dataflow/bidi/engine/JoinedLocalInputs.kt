package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.Facts
import org.opentaint.dataflow.bidi.ap.canonicalPackets
import org.opentaint.dataflow.bidi.ap.GroupKey
import org.opentaint.dataflow.bidi.ap.ApOps
import org.opentaint.dataflow.bidi.ap.ApMode
import org.opentaint.dataflow.bidi.ap.PremiseKey
import org.opentaint.dataflow.bidi.ap.MarkSlot
import org.opentaint.dataflow.bidi.ap.Tail
import org.opentaint.dataflow.bidi.ap.Reach
import org.opentaint.dataflow.bidi.ap.STATIC
import org.opentaint.dataflow.bidi.ap.forEachLeafPosition
import org.opentaint.dataflow.bidi.store.PathTrie
import java.util.BitSet

/** The same table used by live local delivery; it has no callback or runtime owner. */
internal data class LocalInputKey(val link: LocalLink, val group: GroupKey)
internal data class LocalInputValue(val link: LocalLink, var value: Facts)
internal data class LocalInputCandidate(val input: LocalInputValue, val member: Int)
internal class LocalInputDirectory(private val ops: ApOps? = null) {
    private val rows = LinkedHashMap<LocalInputKey, LocalInputValue>()
    private val handles = HashMap<LocalInputKey, Int>()
    private var ordered = ArrayList<LocalInputValue>()
    private var positions: PathTrie<Int>? = PathTrie(ops?.manager?.cancellation)
    private val staticControls = LinkedHashSet<Int>()
    val size: Int get() = rows.size
    val values: Collection<LocalInputValue> get() = rows.values
    operator fun get(key: LocalInputKey): LocalInputValue? = rows[key]
    operator fun set(key: LocalInputKey, value: LocalInputValue) {
        check(key !in rows) { "A local group is updated through its existing value" }
        handles[key] = ordered.size
        ordered += value
        rows[key] = value
    }

    internal fun recordDelta(key: LocalInputKey, delta: Facts) {
        val manager = checkNotNull(ops).manager
        val handle = handles.getValue(key)
        val index = checkNotNull(positions) { "Local candidate selection was released" }
        manager.forEachLeafPosition(delta) { base, path -> index.add(base, path, handle) }
        val input = ordered[handle]
        if (input.link.original.isZero && input.value is Reach) staticControls += handle
    }

    /** Transpose of native publication replay. Geometry is conservative; matching is unchanged.
     * Restore the old row -> input insertion -> member order before any callback can run. */
    internal fun candidates(premise: PremiseKey, mode: ApMode): List<LocalInputCandidate> {
        val index = checkNotNull(positions) { "Local candidate selection was released" }
        val selected = HashMap<Int, BitSet>()
        fun offer(handle: Int, member: Int) { selected.getOrPut(handle) { BitSet(premise.size) }.set(member) }
        for (member in 0 until premise.size) {
            ops?.manager?.cancellation?.checkpoint()
            val initial = premise.member(member)
            for (handle in index.lookupPrefixes(initial.base, initial.pathData)) offer(handle, member)
            if (mode.run1 || initial.mark is MarkSlot.Star || initial.tail == Tail.STAR)
                for (handle in index.lookupExtensions(initial.base, initial.pathData)) offer(handle, member)
            if (mode.run1 && initial.base == STATIC) for (handle in staticControls) offer(handle, member)
        }
        val result = ArrayList<LocalInputCandidate>()
        for (handle in selected.keys.sorted()) {
            val current = ordered[handle]
            val packets = ops?.manager?.canonicalPackets(current.value) ?: listOf(current.value)
            val members = selected.getValue(handle)
            var member = members.nextSetBit(0)
            while (member >= 0) {
                for (packet in packets) result += LocalInputCandidate(LocalInputValue(current.link, packet), member)
                member = members.nextSetBit(member + 1)
            }
        }
        return result
    }

    internal fun visitCanonical(visit: (LocalLink, Facts) -> Unit) {
        for (input in rows.values) for (packet in ops?.manager?.canonicalPackets(input.value) ?: listOf(input.value))
            visit(input.link, packet)
    }

    internal fun releaseCandidateIndex() {
        positions = null
        handles.clear(); ordered = ArrayList(); staticControls.clear()
    }

    fun clear() { rows.clear(); releaseCandidateIndex() }
}

/** Joined ownership of one moved input directory, including saved-only entries. */
internal class JoinedLocalInputs internal constructor(private var directory: LocalInputDirectory?) : AutoCloseable {
    internal val groups: Int get() = checkNotNull(directory) { "Joined local inputs are closed" }.size
    fun visit(visit: (LocalLink, Facts) -> Unit) {
        checkNotNull(directory) { "Joined local inputs are closed" }.visitCanonical(visit)
    }
    override fun close() {
        val owned = directory ?: return
        directory = null
        owned.clear()
    }
}
