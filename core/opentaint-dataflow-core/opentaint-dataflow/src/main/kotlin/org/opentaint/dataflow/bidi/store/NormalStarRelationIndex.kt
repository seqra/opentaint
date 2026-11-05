package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*

/** Current pure NORMAL STAR relations at one exact interface. The input trie fixes the
 * shared residual; packed output DAGs test its correlated counterpart without listing paths. */
internal class NormalStarRelationIndex(
    private val m: ApManager,
    private val interners: StoreInterners,
    private val emptied: (InitialAp) -> Unit = {},
) {
    private data class Header(val base: AccessPathBase, val mx: MarkExclusions)
    class Update(val fresh: List<FlowTree>, val affectedInitials: Set<InitialAp>)
    private val current = LinkedHashMap<InitialAp, LinkedHashMap<Header, FlowTree>>()
    private val byInput = PathTrie<InitialAp>(m.cancellation)

    fun supports(initial: PremiseKey, facts: Facts): Boolean = initial is InitialAp &&
        initial.manager === m && initial.isFlow && initial.mark == MarkSlot.STAR &&
        initial.tail == Tail.STAR && initial.exclusion == ExclusionSet.Empty &&
        initial.base != AccessPathBase.Zero && initial.base != STATIC && facts is FlowTree &&
        facts.layer == Layer.NORMAL && facts.tail == Tail.STAR && facts.exclusion == ExclusionSet.Empty &&
        facts.base != AccessPathBase.Zero && facts.base != STATIC

    private fun append(root: FlowNode, residual: IntArray): FlowNode {
        if (residual.isEmpty()) return root
        val suffix = FlowAlgebra.prepend(m, m.path(residual.asList()), FlowAlgebra.LEAF_NODE)
        return checkNotNull(FlowAlgebra.graft(root, { it == FlowLeaf.LEAF }, suffix, m.cancellation))
    }

    private fun canonical(rows: Iterable<FlowTree>): LinkedHashMap<Header, FlowTree> {
        // FlowGroup owns one output base, as in ConclusionGroup. An input can
        // independently return, preserve an argument, and update a local.
        val groups = LinkedHashMap<AccessPathBase, FlowGroup>()
        for (row in rows) groups.getOrPut(row.base) { FlowGroup(m, interners.flow) }.addAll(row)
        return groups.values.asSequence().flatMap { it.all() }
            .associateByTo(LinkedHashMap()) { Header(it.base, it.markExclusion) }
    }

    private fun replace(initial: InitialAp, rows: LinkedHashMap<Header, FlowTree>, affected: MutableSet<InitialAp>) {
        if (current[initial] == rows || (current[initial] == null && rows.isEmpty())) return
        affected += initial
        if (rows.isEmpty()) {
            current.remove(initial)
            byInput.remove(initial.base, initial.pathData, initial)
            emptied(initial)
        } else {
            if (!current.containsKey(initial)) byInput.add(initial.base, initial.pathData, initial)
            current[initial] = rows
        }
    }

    fun add(initial: InitialAp, offered: FlowTree): Update {
        require(supports(initial, offered))
        val previous = current[initial]?.toMap().orEmpty()
        var rows = canonical(previous.values + offered)
        // Preserve native same-input T2/mx coalescing before cross-input cover.
        // A changed header can expose another exact-header ancestor; settle locally.
        while (true) {
            val filtered = ArrayList<FlowTree>()
            for ((header, value) in rows) {
                var root: FlowNode? = value.root
                for (short in byInput.lookupPrefixes(initial.base, initial.pathData)) {
                    if (short === initial) continue
                    val residual = initial.pathData.copyOfRange(short.pathData.size, initial.pathData.size)
                    for (cover in current.getValue(short).values) {
                        if (cover.base != value.base || !cover.markExclusion.isSubsetOf(value.markExclusion)) continue
                        root = root?.let { FlowAlgebra.minusNode(it, append(cover.root, residual), m.cancellation) }
                        if (root == null) break
                    }
                    if (root == null) break
                }
                root?.let { filtered += value.withRoot(it) }
            }
            val next = canonical(filtered)
            if (next == rows) break
            rows = next
        }
        val affected = LinkedHashSet<InitialAp>()
        replace(initial, rows, affected)
        val pending = java.util.ArrayDeque<InitialAp>()
        if (affected.isNotEmpty() && rows.isNotEmpty()) pending.add(initial)
        while (pending.isNotEmpty()) {
            m.cancellation.checkpoint()
            val short = pending.removeFirst()
            val covers = current[short] ?: continue
            for (long in byInput.lookupExtensions(short.base, short.pathData)) {
                if (long === short) continue
                val old = current.getValue(long)
                val residual = long.pathData.copyOfRange(short.pathData.size, long.pathData.size)
                val remaining = ArrayList<FlowTree>()
                for ((header, value) in old) {
                    var root: FlowNode? = value.root
                    for (cover in covers.values) {
                        if (cover.base != value.base || !cover.markExclusion.isSubsetOf(value.markExclusion)) continue
                        root = root?.let { FlowAlgebra.minusNode(it, append(cover.root, residual), m.cancellation) }
                        if (root == null) break
                    }
                    root?.let { remaining += value.withRoot(it) }
                }
                val next = canonical(remaining)
                if (next != old) {
                    replace(long, next, affected)
                    if (next.isNotEmpty()) pending.add(long)
                }
            }
        }
        val fresh = ArrayList<FlowTree>()
        for ((header, value) in current[initial].orEmpty()) {
            val old = previous[header]
            val root = if (old == null) value.root else FlowAlgebra.minusNode(value.root, old.root, m.cancellation)
            root?.let { fresh += value.withRoot(it) }
        }
        return Update(fresh, affected)
    }

    fun all(): Sequence<Pair<InitialAp, FlowTree>> = sequence {
        for ((initial, headers) in current) for (facts in headers.values) {
            m.cancellation.checkpoint(); yield(initial to facts)
        }
    }

    fun borrowExact(initial: PremiseKey): Sequence<FlowTree> = current[initial]?.values?.asSequence() ?: emptySequence()

    /** Current-coordinate intersection of a detached publication; no historical payload. */
    fun retainCurrent(initial: InitialAp, offered: FlowTree): FlowTree? {
        if (!supports(initial, offered)) return offered
        val kept = current[initial]?.get(Header(offered.base, offered.markExclusion)) ?: return null
        val removed = FlowAlgebra.minusNode(offered.root, kept.root, m.cancellation) ?: return offered
        val root = FlowAlgebra.minusNode(offered.root, removed, m.cancellation) ?: return null
        return offered.withRoot(root)
    }

    /** Stronger transient S specializations for existing marked-compaction rules.
     * Grafting preserves DAG sharing and creates no hypothetical InitialAp. */
    fun visitSpecializedCovers(shape: InitialAp, emit: (FlowTree) -> Unit) {
        if (shape.tail != Tail.STAR || shape.exclusion != ExclusionSet.Empty || shape.mark != MarkSlot.STAR) return
        val input = shape.pathData
        for (short in byInput.lookupPrefixes(shape.base, input)) {
            m.cancellation.checkpoint()
            val residual = input.copyOfRange(short.pathData.size, input.size)
            for (header in current.getValue(short).values) emit(header.withRoot(append(header.root, residual)))
        }
    }
}
