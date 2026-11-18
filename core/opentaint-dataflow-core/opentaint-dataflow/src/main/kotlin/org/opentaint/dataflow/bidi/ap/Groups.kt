package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.SoftReferenceManager

/** FLOW values for one base, separated by layer and both exclusions. One store writer owns this group. */
class FlowGroup(private val m: ApManager, private val interner: TrieInterner<FlowLeaf>) {
    private val trees = arrayOf(ArrayList<FlowTree>(1), ArrayList<FlowTree>(1))

    fun all(): Sequence<FlowTree> = trees[0].asSequence() + trees[1].asSequence()

    /** T4: return the new part, or the merged value when T2 changes an annotation. */
    private fun insert(t: FlowTree): FlowTree? {
        val list = trees[t.layer.ordinal]
        var pending = t
        while (true) {
            m.cancellation.checkpoint()
            val i = list.indexOfFirst {
                m.cancellation.checkpoint()
                it.tail == pending.tail && it.exclusion == pending.exclusion && it.markExclusion == pending.markExclusion
            }
            if (i >= 0) {
                val rest = subtractSubsumed(pending, list) ?: return null
                val (merged, delta) = FlowAlgebra.mergeAddDelta(list[i].root, rest.root, m.cancellation)
                if (delta == null) return null
                list[i] = list[i].withRoot(interner.internIfRequired(merged))
                return m.flowTree(pending.base, pending.layer, pending.exclusion, pending.markExclusion, delta, pending.tail)
            }

            val k = list.indexOfFirst {
                m.cancellation.checkpoint()
                it.tail == pending.tail && it.root == pending.root &&
                    (it.markExclusion == pending.markExclusion || it.exclusion == pending.exclusion)
            }
            if (k >= 0) {
                val stored = list[k]
                val merged = m.flowTree(pending.base, pending.layer,
                    stored.exclusion.intersect(pending.exclusion),
                    stored.markExclusion.intersect(pending.markExclusion), stored.root, pending.tail)
                if (merged.exclusion == stored.exclusion && merged.markExclusion == stored.markExclusion) return null
                list.removeAt(k)
                pending = merged
                continue
            }

            val fresh = subtractSubsumed(pending, list) ?: return null
            list += fresh.withRoot(interner.internIfRequired(fresh.root))
            return fresh
        }
    }

    fun add(t: FlowTree): FlowTree? = addAll(t).also {
        check(it.size <= 1) { "Use addAll for multiple canonical FLOW headers" }
    }.singleOrNull()

    fun addAll(t: FlowTree): List<FlowTree> {
        val list = trees[t.layer.ordinal]
        val before = list.toList()
        insert(t)
        // Fill one complete immediate MUST branch at a time. Each promotion
        // strictly reduces a finite exclusion; admitted headers are canonical.
        while (true) {
            val canonical = list.mapNotNull { row ->
                subtractSubsumed(compactPacket(row),list.filter { it !== row })
            }
            list.clear(); list.addAll(canonical)
            if (mergeMustOverlap(list)) continue
            var promoted: FlowTree? = null
            outer@ for (parent in list.toList()) {
                if (parent.tail != Tail.ANY_TAINT) continue
                val fields = (parent.exclusion as? ExclusionSet.Concrete)?.ids ?: continue
                m.forEachLeafPosition(parent) { _, path ->
                    if (promoted != null) return@forEachLeafPosition
                    for (field in fields) {
                        val full = list.any { child ->
                            child.tail == Tail.ANY_TAINT && child.exclusion == ExclusionSet.Empty &&
                                child.markExclusion.isSubsetOf(parent.markExclusion) &&
                                child.root.walk(path + field) { _, _ -> m.cancellation.checkpoint() }
                                    ?.leaf?.isEmpty == false
                        }
                        if (!full) continue
                        val e = ExclusionSet.of(fields.filter { it != field }.toIntArray())
                        val root = FlowAlgebra.prepend(m,m.path(path.asList()),FlowAlgebra.LEAF_NODE)
                        val candidate = m.flowTree(parent.base,parent.layer,e,parent.markExclusion,root,parent.tail)
                        if (subtractSubsumed(candidate,list) != null) { promoted = candidate; break }
                    }
                }
                if (promoted != null) break@outer
            }
            if (promoted == null) break
            insert(promoted!!)
        }
        // Prune old descendants too. This makes parent-first and child-first
        // insertion expose the same current basis.
        val canonical = list.mapNotNull { row ->
            subtractSubsumed(compactPacket(row),list.filter { it !== row })
        }
        list.clear(); list.addAll(canonical)
        return canonical.mapNotNull { row ->
            var root: FlowNode? = row.root
            for (old in before) {
                if (old.groupKey == row.groupKey) root = root?.let {
                    FlowAlgebra.minusNode(it,old.root,m.cancellation)
                }
            }
            root?.let { row.withRoot(it) }
        }
    }

    private fun mergeMustOverlap(list: MutableList<FlowTree>): Boolean {
        for (i in list.indices) for (j in i+1 until list.size) {
            val a = list[i]; val b = list[j]
            if (a.tail != Tail.ANY_TAINT || b.tail != Tail.ANY_TAINT ||
                a.exclusion == b.exclusion && a.markExclusion == b.markExclusion ||
                a.exclusion != b.exclusion && a.markExclusion != b.markExclusion) continue
            val diff = FlowAlgebra.minusNode(a.root,b.root,m.cancellation)
            val common = if (diff == null) a.root else
                FlowAlgebra.minusNode(a.root,diff,m.cancellation) ?: continue
            val merged = m.flowTree(a.base,a.layer,a.exclusion.intersect(b.exclusion),
                a.markExclusion.intersect(b.markExclusion),common,a.tail)
            val ar = FlowAlgebra.minusNode(a.root,common,m.cancellation)
            val br = FlowAlgebra.minusNode(b.root,common,m.cancellation)
            if (br == null) list.removeAt(j) else list[j] = b.withRoot(br)
            if (ar == null) list.removeAt(i) else list[i] = a.withRoot(ar)
            insert(merged)
            return true
        }
        return false
    }

    private fun compactPacket(row: FlowTree): FlowTree {
        if (row.tail != Tail.ANY && row.tail != Tail.ANY_TAINT) return row
        var root = row.root
        FlowAlgebra.forEachLeafPosition(row.root,m.cancellation) { path ->
            var node = row.root
            var covered = false
            for (field in path) {
                if (!node.leaf.isEmpty && (row.tail == Tail.ANY || row.exclusion.admits(field))) {
                    covered = true; break
                }
                node = checkNotNull(node.child(field))
            }
            if (covered) {
                val at = FlowAlgebra.prepend(m,m.path(path.asList()),FlowAlgebra.LEAF_NODE)
                root = checkNotNull(FlowAlgebra.minusNode(root,at,m.cancellation))
            }
        }
        return if (root === row.root) row else row.withRoot(root)
    }

    private fun subtractSubsumed(t: FlowTree, others: List<FlowTree>): FlowTree? {
        var root = t.root
        for (stored in others) {
            m.cancellation.checkpoint()
            val marks = stored.markExclusion.isSubsetOf(t.markExclusion)
            val atOk = marks && when (stored.tail) {
                Tail.ANY -> true
                Tail.STAR -> t.tail == Tail.STAR && stored.exclusion.isSubsetOf(t.exclusion)
                Tail.EXACT -> t.tail == Tail.EXACT && stored.exclusion.isSubsetOf(t.exclusion)
                Tail.ANY_TAINT -> t.tail == Tail.ANY_TAINT && stored.exclusion.isSubsetOf(t.exclusion)
            }
            val belowOk = marks && (stored.tail == Tail.ANY ||
                stored.tail == Tail.ANY_TAINT && t.tail == Tail.ANY_TAINT)
            root = FlowAlgebra.subtract(root, stored.root, FlowLeaf.NONE,
                at = { if (atOk) it else FlowLeaf.NONE },
                below = { if (belowOk) it else FlowLeaf.NONE },
                admits = stored.exclusion::admits, cancellation = m.cancellation) ?: return null
        }
        return if (root === t.root) t else t.withRoot(root)
    }
}

/** Construct a store result after its mask is proved to be included in root.
 * This is coordinate inclusion, not AP prefix coverage. General factories still trim. */
private fun admittedTree(
    m: ApManager, header: TaintTree, root: TaintNode, includedMask: TaintNode?,
    exclusion: ExclusionSet = header.exclusion,
): TaintTree = TaintTree(
    header.base, header.layer, root,
    if (!root.hasAny || header.anyTail == Tail.ANY) ExclusionSet.Empty else m.intern(exclusion),
    if (root.hasAny) header.anyTail else Tail.ANY_TAINT,
    includedMask,
)

/** TAINT values for one base. STAR and must spans keep distinct suffix semantics. */
class TaintGroup(private val m: ApManager, private val interner: TrieInterner<TaintLeaves>) {
    private val trees = Array(4) { ArrayList<TaintTree>(1) }
    private fun lane(t: TaintTree) = t.layer.ordinal * 2 + if (t.protectionClass()) 1 else 0
    fun all(): Sequence<TaintTree> = trees.asSequence().flatMap { it.asSequence() }

    internal fun restoreCurrent(t: TaintTree) {
        val list = trees[lane(t)]
        check(list.none { it.anyTail == t.anyTail && it.exclusion == t.exclusion })
        list += t
    }

    /** Convenience for a scalar/header offer. Runtime owners use the complete batch API. */
    fun add(t: TaintTree): TaintTree? = addAll(t).let { result ->
        check(result.size <= 1) { "Canonical TAINT admission produced several headers; use addAll" }
        result.singleOrNull()
    }

    fun addAll(t: TaintTree): List<TaintTree> {
        m.cancellation.checkpoint()
        val result = ArrayList<TaintTree>()
        for (part in t.membershipPackets(m)) {
            val packet = part as TaintTree
            val authority = trees[lane(packet)]
            val before = authority.toList()
            val list = authority.toMutableList()
            if (!mergeHeader(list, packet)) continue
            canonicalize(list)
            authority.clear()
            authority.addAll(list)
            for (retained in list) {
                val old = before.firstOrNull { sameHeader(it, retained) }
                val fresh = if (old == null) retained.root else
                    m.taintAlg.minusNode(retained.root, old.root, m.cancellation) ?: continue
                result += packet(retained, fresh)
            }
        }
        return result
    }

    private fun sameHeader(a: TaintTree, b: TaintTree) =
        a.anyTail == b.anyTail && a.exclusion == b.exclusion

    private fun packet(header: TaintTree, root: TaintNode,
                       exclusion: ExclusionSet = header.exclusion): TaintTree {
        if (root === header.root && exclusion == header.exclusion) return header
        val owned = interner.internIfRequired(root)
        return admittedTree(m, header, owned,
            if (header.protectionClass()) owned else null, exclusion)
    }

    private fun mergeHeader(list: MutableList<TaintTree>, value: TaintTree): Boolean {
        val index = list.indexOfFirst { sameHeader(it, value) }
        if (index < 0) list += value else {
            val old = list[index]
            val merged = m.taintAlg.mergeAdd(old.root, value.root, m.cancellation)
            if (merged === old.root || merged == old.root) return false
            list[index] = packet(old, merged)
        }
        return true
    }

    private fun removeCoordinates(list: MutableList<TaintTree>, index: Int, mask: TaintNode) {
        val old = list[index]
        val remaining = m.taintAlg.minusNode(old.root, mask, m.cancellation)
        if (remaining == null) list.removeAt(index) else list[index] = packet(old, remaining)
    }

    private fun canonicalize(list: MutableList<TaintTree>) {
        while (true) {
            m.cancellation.checkpoint()
            if (mergeEqualHeaders(list) || mergeSpanExclusions(list) || fillMustHole(list)) continue
            var changed = false
            for (i in list.indices) {
                val value = list[i]
                if (value.anyTail == Tail.ANY || value.anyTail == Tail.ANY_TAINT) {
                    val may = value.anyTail == Tail.ANY
                    val compact = m.taintAlg.subtract(value.root, value.root, TaintLeaves.EMPTY,
                        at = { leaf -> if (may) m.taintLeaves(leaf.any, MarkSet.EMPTY) else TaintLeaves.EMPTY },
                        below = { leaf -> m.taintLeaves(if (may) leaf.any else MarkSet.EMPTY, leaf.any) },
                        admits = value.exclusion::admits, cancellation = m.cancellation)
                    checkNotNull(compact) { "An ancestor-canonical packet retains its first leaf" }
                    if (compact != value.root) { list[i] = packet(value, compact); changed = true }
                }
            }
            for (i in list.indices.reversed()) {
                val old = list[i]
                val kept = subtractSubsumed(old, list.filterIndexed { index, _ -> index != i })
                if (kept == null) { list.removeAt(i); changed = true }
                else if (kept.root != old.root) { list[i] = kept; changed = true }
            }
            if (!changed) return
        }
    }

    private fun mergeEqualHeaders(list: MutableList<TaintTree>): Boolean {
        for (i in list.indices) for (j in i + 1 until list.size) {
            if (!sameHeader(list[i], list[j])) continue
            list[i] = packet(list[i], m.taintAlg.mergeAdd(list[i].root, list[j].root, m.cancellation))
            list.removeAt(j)
            return true
        }
        return false
    }

    /** Compare mark masks at equal coordinates; do not enumerate runtime marks. */
    private fun mergeSpanExclusions(list: MutableList<TaintTree>): Boolean {
        for (i in list.indices) {
            val a = list[i]
            if ((a.anyTail != Tail.ANY_TAINT && a.anyTail != Tail.STAR) || !a.root.hasAny) continue
            for (j in i + 1 until list.size) {
                val b = list[j]
                if (b.anyTail != a.anyTail || a.exclusion == b.exclusion) continue
                val overlap = intersectTaintMask(a.root, b.root, m.cancellation)?.let {
                    m.taintAlg.mapLeaves(it, m.cancellation) { leaf -> m.taintLeaves(MarkSet.EMPTY, leaf.any) }
                } ?: continue
                val merged = packet(a, overlap, a.exclusion.intersect(b.exclusion))
                // Remove common coordinates first; the replacement owns their union.
                removeCoordinates(list, j, overlap)
                removeCoordinates(list, i, overlap)
                mergeHeader(list, merged)
                return true
            }
        }
        return false
    }

    private fun fillMustHole(list: MutableList<TaintTree>): Boolean {
        for (i in list.indices) {
            val parent = list[i]
            val excluded = parent.exclusion as? ExclusionSet.Concrete ?: continue
            if (parent.anyTail != Tail.ANY_TAINT) continue
            val child = list.firstOrNull { it.anyTail == Tail.ANY_TAINT && it.exclusion == ExclusionSet.Empty }
                ?: continue
            var fill: Pair<TaintNode, Int>? = null
            m.taintAlg.forEachLeaf(parent.root, EMPTY_PATH, m.cancellation) { path, leaf ->
                if (fill == null && !leaf.any.isEmpty) for (field in excluded.data) {
                    val childLeaf = child.root.walk(path + field)?.leaf ?: continue
                    val marks = leaf.any intersect childLeaf.any
                    if (!marks.isEmpty) {
                        fill = m.taintAlg.prepend(m, m.path(path),
                            m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, marks))) to field
                        break
                    }
                }
            }
            val (mask, field) = fill ?: continue
            val merged = packet(parent, mask, ExclusionSet.of(excluded.data.filter { it != field }.toIntArray()))
            removeCoordinates(list, i, mask)
            mergeHeader(list, merged)
            return true
        }
        return false
    }

    private fun subtractSubsumed(t: TaintTree, others: List<TaintTree>): TaintTree? {
        val alg = m.taintAlg
        var remaining = t.root
        for (stored in others) {
            m.cancellation.checkpoint()
            val may = stored.anyTail == Tail.ANY
            val star = stored.anyTail == Tail.STAR
            val coversAny = may || stored.anyTail == t.anyTail
            val atAny = coversAny && (may || stored.exclusion.isSubsetOf(t.exclusion))
            remaining = alg.subtract(remaining, stored.root, TaintLeaves.EMPTY,
                at = { alg.leaves(if (may) it.exact + it.any else it.exact,
                    if (atAny) it.any else MarkSet.EMPTY) },
                below = { alg.leaves(if (may) it.any else MarkSet.EMPTY,
                    if (coversAny && !star) it.any else MarkSet.EMPTY) },
                admits = stored.exclusion::admits, cancellation = m.cancellation) ?: return null
        }
        return if (remaining === t.root) t else packet(t, remaining)
    }
}

/** All conclusion bases and kinds for one premise key. REACH has one bit per layer. */
class ConclusionGroup(private val m: ApManager, private val interners: StoreInterners) {
    private val reach = BooleanArray(2)
    private val flow = HashMap<AccessPathBase, FlowGroup>(2)
    private val taint = HashMap<AccessPathBase, TaintGroup>(2)

    fun addAll(f: Facts): List<Facts> = f.membershipPackets(m).flatMap {
        when (it) {
            is TaintTree -> taint.getOrPut(it.base) { TaintGroup(m, interners.taint) }.addAll(it)
            is FlowTree -> flow.getOrPut(it.base) { FlowGroup(m, interners.flow) }.addAll(it)
            is Reach -> listOfNotNull(add(it))
        }
    }

    fun add(f: Facts): Facts? {
        m.cancellation.checkpoint()
        return when (f) {
            is Reach -> if (reach[f.layer.ordinal]) null else f.also { reach[f.layer.ordinal] = true }
            is FlowTree -> flow.getOrPut(f.base) { FlowGroup(m, interners.flow) }.add(f)
            is TaintTree -> taint.getOrPut(f.base) { TaintGroup(m, interners.taint) }.add(f)
        }
    }

    fun all(): Sequence<Facts> = Layer.entries.asSequence().filter { reach[it.ordinal] }.map(Reach::of) +
        flow.values.asSequence().flatMap { it.all() } + taint.values.asSequence().flatMap { it.all() }
}

/** Soft trie caches for one store, with a separate table for each leaf kind. */
class StoreInterners(refs: SoftReferenceManager, private val cancellation: Cancellation) {
    val flow = TrieInterner<FlowLeaf>(refs, cancellation)
    val taint = TrieInterner<TaintLeaves>(refs, cancellation)

    fun internIfRequired(f: Facts): Facts {
        cancellation.checkpoint()
        return when (f) {
            is Reach -> f
            is FlowTree -> flow.internIfRequired(f.root).let { if (it === f.root) f else f.withRoot(it) }
            is TaintTree -> taint.internIfRequired(f.root).let { if (it === f.root) f else f.withRoot(it) }
        }
    }
}
