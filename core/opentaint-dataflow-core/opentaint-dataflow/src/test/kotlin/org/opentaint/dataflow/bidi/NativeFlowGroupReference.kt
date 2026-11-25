package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*

/** Test reference: the native `FlowGroup` of `29c78d5c3` (`ap/Groups.kt` lines 8-172), before P3
 * (spec/next-iteration-p3-p2m-implementation.md §3.5). Only the name, the test counters and
 * [isFixpoint] are new. Do not change the copied code: the P3 tests compare the landed group with it. */
internal class NativeFlowGroupReference(private val m: ApManager, private val interner: TrieInterner<FlowLeaf>) {
    /** Test-only counts of the MUST merges and the promotions that this reference did. */
    var mustMerges = 0
        private set
    var promotions = 0
        private set

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
            if (mergeMustOverlap(list)) { mustMerges++; continue }
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
            promotions++
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

    /** Invariant F: a full pass, the MUST merge and the promotion change nothing in [list] (one layer).
     * The check runs on a scratch reference, so it does not change this one. */
    fun isFixpoint(list: List<FlowTree>): Boolean {
        val scratch = NativeFlowGroupReference(m, interner)
        val rows = scratch.trees[list.firstOrNull()?.layer?.ordinal ?: return true]
        rows.addAll(list)
        val pass = rows.mapNotNull { row -> scratch.subtractSubsumed(scratch.compactPacket(row), rows.filter { it !== row }) }
        if (pass != list) return false
        if (scratch.mergeMustOverlap(rows)) return false
        return scratch.promotionOf(rows) == null
    }

    /** The promotion scan of [addAll], for [isFixpoint]. */
    private fun promotionOf(list: List<FlowTree>): FlowTree? {
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
        return promoted
    }
}
