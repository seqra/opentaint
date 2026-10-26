package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.SoftReferenceManager

/** FLOW values for one base, separated by layer and both exclusions. One store writer owns this group. */
class FlowGroup(private val m: ApManager, private val interner: TrieInterner<FlowLeaf>) {
    private val trees = arrayOf(ArrayList<FlowTree>(1), ArrayList<FlowTree>(1))

    fun all(): Sequence<FlowTree> = trees[0].asSequence() + trees[1].asSequence()

    /** T4: return the new part, or the merged value when T2 changes an annotation. */
    fun add(t: FlowTree): FlowTree? {
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

    private fun subtractSubsumed(t: FlowTree, others: List<FlowTree>): FlowTree? {
        var root = t.root
        for (stored in others) {
            m.cancellation.checkpoint()
            val marks = stored.markExclusion.isSubsetOf(t.markExclusion)
            val atOk = marks && (stored.tail == Tail.ANY ||
                (t.tail == Tail.STAR && stored.exclusion.isSubsetOf(t.exclusion)))
            val belowOk = marks && stored.tail == Tail.ANY
            root = FlowAlgebra.subtract(root, stored.root, FlowLeaf.NONE,
                at = { if (atOk) it else FlowLeaf.NONE },
                below = { if (belowOk) it else FlowLeaf.NONE },
                cancellation = m.cancellation) ?: return null
        }
        return if (root === t.root) t else t.withRoot(root)
    }
}

/** TAINT values for one base. STAR and must spans keep distinct suffix semantics. */
class TaintGroup(private val m: ApManager, private val interner: TrieInterner<TaintLeaves>) {
    private val trees = arrayOf(ArrayList<TaintTree>(1), ArrayList<TaintTree>(1))

    fun all(): Sequence<TaintTree> = trees[0].asSequence() + trees[1].asSequence()

    /** Restore one complete current typed header for a temporary admission
     * adapter. Do not re-admit the snapshot: that would compact old STAR rows
     * merely because a later ANY row is already present. No history is kept. */
    internal fun restoreCurrent(t: TaintTree) {
        m.cancellation.checkpoint()
        val list = trees[t.layer.ordinal]
        check(list.none { it.anyTail == t.anyTail && it.exclusion == t.exclusion })
        list += t
    }

    fun add(t: TaintTree): TaintTree? {
        val alg = m.taintAlg
        val list = trees[t.layer.ordinal]
        var pending = t
        while (true) {
            m.cancellation.checkpoint()
            val sameKey = list.indexOfFirst {
                m.cancellation.checkpoint()
                it.anyTail == pending.anyTail && it.exclusion == pending.exclusion
            }
            if (sameKey < 0) {
                val k = list.indexOfFirst {
                    m.cancellation.checkpoint()
                    it.anyTail == pending.anyTail && it.root == pending.root
                }
                if (k >= 0) {
                    val stored = list[k]
                    val exclusion = stored.exclusion.intersect(pending.exclusion)
                    // Equal ordinary content can still carry a new protected membership.
                    if (exclusion == stored.exclusion) {
                        val rest = subtractSubsumed(pending, list) ?: return null
                        val protection = mergeProtection(stored.nonSubsumable, rest.nonSubsumable)
                        val root = alg.mergeAdd(stored.root, rest.root, m.cancellation)
                        list[k] = stored.withRoot(interner.internIfRequired(root)).withProtection(protection)
                        return rest
                    }
                    list.removeAt(k)
                    pending = m.taintTree(pending.base, pending.layer, stored.root, exclusion, pending.anyTail)
                        .withProtection(mergeProtection(stored.nonSubsumable, pending.nonSubsumable))
                    continue
                }
            }

            val rest = subtractSubsumed(pending, list) ?: return null
            // Subtraction can remove the last must leaf. Its canonical key is then Empty E.
            val i = list.indexOfFirst {
                m.cancellation.checkpoint()
                it.anyTail == rest.anyTail && it.exclusion == rest.exclusion
            }
            if (i < 0) {
                list += rest.withRoot(interner.internIfRequired(rest.root))
                return rest
            }
            val stored = list[i]
            val (merged, delta) = alg.mergeAddDelta(stored.root, rest.root, m.cancellation)
            val protection = mergeProtection(stored.nonSubsumable, rest.nonSubsumable)
            val deltaRoot = mergeProtection(delta, rest.nonSubsumable) ?: return null
            list[i] = stored.withRoot(interner.internIfRequired(merged)).withProtection(protection)
            return m.taintTree(pending.base, pending.layer, deltaRoot, rest.exclusion, rest.anyTail)
                .withProtection(rest.nonSubsumable)
        }
    }

    private fun subtractSubsumed(t: TaintTree, others: List<TaintTree>): TaintTree? {
        val ordinary = subtract(t.root, t, others, protectedOnly = false)
        // Ordinary ANY coverage cannot consume a fresh protected EXACT dependency.
        val protection = t.nonSubsumable?.let { subtract(it, t, others, protectedOnly = true) }
        val root = mergeProtection(ordinary, protection) ?: return null
        if (root === t.root && protection === t.nonSubsumable) return t
        return t.withRoot(root).withProtection(protection)
    }

    private fun mergeProtection(a: TaintNode?, b: TaintNode?): TaintNode? = when {
        a == null -> b
        b == null -> a
        else -> m.taintAlg.mergeAdd(a, b, m.cancellation)
    }

    private fun subtract(root: TaintNode, t: TaintTree, others: List<TaintTree>,
                         protectedOnly: Boolean): TaintNode? {
        val alg = m.taintAlg
        var remaining = root
        for (stored in others) {
            m.cancellation.checkpoint()
            val storedRoot = if (protectedOnly) stored.nonSubsumable ?: continue else stored.root
            val storedMay = stored.anyTail == Tail.ANY
            val storedStar = stored.anyTail == Tail.STAR
            val coversAny = storedMay || stored.anyTail == t.anyTail
            val anyAt = coversAny && (storedMay || stored.exclusion.isSubsetOf(t.exclusion))
            remaining = alg.subtract(remaining, storedRoot, TaintLeaves.EMPTY,
                at = { alg.leaves(if (storedMay) it.exact + it.any else it.exact,
                    if (anyAt) it.any else MarkSet.EMPTY) },
                below = { alg.leaves(if (storedMay) it.any else MarkSet.EMPTY,
                    if (coversAny && !storedStar) it.any else MarkSet.EMPTY) },
                admits = stored.exclusion::admits,
                cancellation = m.cancellation) ?: return null
        }
        return remaining
    }
}

/** All conclusion bases and kinds for one premise key. REACH has one bit per layer. */
class ConclusionGroup(private val m: ApManager, private val interners: StoreInterners) {
    private val reach = BooleanArray(2)
    private val flow = HashMap<AccessPathBase, FlowGroup>(2)
    private val taint = HashMap<AccessPathBase, TaintGroup>(2)

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
