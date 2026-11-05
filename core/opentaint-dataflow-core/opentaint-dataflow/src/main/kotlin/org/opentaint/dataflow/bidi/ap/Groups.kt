package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.SoftReferenceManager

/** FLOW values for one base, separated by layer and both exclusions. One store writer owns this group. */
class FlowGroup(private val m: ApManager, private val interner: TrieInterner<FlowLeaf>) {
    private val trees = arrayOf(ArrayList<FlowTree>(1), ArrayList<FlowTree>(1))

    fun all(): Sequence<FlowTree> = trees[0].asSequence() + trees[1].asSequence()

    /** T4: return the new part, or the merged value when T2 changes an annotation. */
    fun add(t: FlowTree): FlowTree? = addAll(t).also {
        check(it.size <= 1) { "Canonical admission has multiple headers; use addAll" }
    }.singleOrNull()

    fun addAll(t: FlowTree): List<FlowTree> {
        m.cancellation.checkpoint()
        val before = trees[t.layer.ordinal]
        if (t.tail != Tail.ANY && t.tail != Tail.ANY_TAINT)
            return addInto(t,before)?.let(::listOf) ?: emptyList()
        if (before.isEmpty()) {
            val canonical = m.canonicalFlowPacket(t)
            val root = interner.internIfRequired(canonical.root)
            val stored = if (root === canonical.root) canonical else canonical.withRoot(root)
            trees[t.layer.ordinal] = arrayListOf(stored)
            return listOf(stored)
        }
        val staged = ArrayList(before)
        if (addInto(t, staged) == null) return emptyList()
        val after = m.canonicalFlowState(staged)
        val changes = ArrayList<FlowTree>()
        for (value in after) {
            val fresh = subtractSubsumed(value,before) ?: continue
            changes += fresh
        }
        m.cancellation.checkpoint()
        trees[t.layer.ordinal] = ArrayList(after.map { it.withRoot(interner.internIfRequired(it.root)) })
        return changes
    }

    private fun addInto(t: FlowTree, list: ArrayList<FlowTree>): FlowTree? {
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
                admits = stored.exclusion::admits,
                cancellation = m.cancellation) ?: return null
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

    fun add(t: TaintTree): TaintTree? = addAll(t).also {
        check(it.size <= 1) { "Canonical admission has multiple headers; use addAll" }
    }.singleOrNull()

    fun addAll(t: TaintTree): List<TaintTree> {
        m.cancellation.checkpoint()
        val before = trees[t.layer.ordinal]
        if (!t.root.hasAny || t.anyTail != Tail.ANY && t.anyTail != Tail.ANY_TAINT)
            return addInto(t,before)?.let(::listOf) ?: emptyList()
        if (before.isEmpty()) {
            val canonical = m.canonicalTaintPacket(t)
            val root = interner.internIfRequired(canonical.root)
            val stored = if (root === canonical.root) canonical
                else admittedTree(m,canonical,root,canonical.nonSubsumable)
            trees[t.layer.ordinal] = arrayListOf(stored)
            return listOf(stored)
        }
        // Ordinary and protected E provenance must remain separate until the
        // two streams are normalized. The old equal-root admission intersects
        // E before unioning masks and would broaden one-sided protection.
        if (subtractSubsumed(t,before) == null) return emptyList()
        val after = m.canonicalTaintState(before + t)
        val changes = ArrayList<TaintTree>()
        for (value in after) {
            val fresh = subtractSubsumed(value,before) ?: continue
            // Preserve T4's whole mixed-content delta only for an actual
            // equal-content E weakening; unrelated old exact siblings are not fresh.
            val wholeEJoin = before.any { old -> old.root.hasAny && old.root == t.root &&
                old.anyTail == t.anyTail && old.exclusion != t.exclusion &&
                value.anyTail == t.anyTail && value.root == t.root &&
                value.exclusion == old.exclusion.intersect(t.exclusion) && value.exclusion != old.exclusion }
            changes += if (wholeEJoin) value else fresh
        }
        m.cancellation.checkpoint()
        trees[t.layer.ordinal] = ArrayList(after.map {
            admittedTree(m,it,interner.internIfRequired(it.root),it.nonSubsumable)
        })
        return changes
    }

    private fun addInto(t: TaintTree, list: ArrayList<TaintTree>): TaintTree? {
        val alg = m.taintAlg
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
                        list[k] = admittedTree(m, stored, interner.internIfRequired(root), protection)
                        return rest
                    }
                    list.removeAt(k)
                    pending = admittedTree(m, pending, stored.root,
                        mergeProtection(stored.nonSubsumable, pending.nonSubsumable), exclusion)
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
                list += admittedTree(m, rest, interner.internIfRequired(rest.root), rest.nonSubsumable)
                return rest
            }
            val stored = list[i]
            val (merged, delta) = alg.mergeAddDelta(stored.root, rest.root, m.cancellation)
            val protection = mergeProtection(stored.nonSubsumable, rest.nonSubsumable)
            val deltaRoot = mergeProtection(delta, rest.nonSubsumable) ?: return null
            list[i] = admittedTree(m, stored, interner.internIfRequired(merged), protection)
            return admittedTree(m, rest, deltaRoot, rest.nonSubsumable)
        }
    }

    private fun subtractSubsumed(t: TaintTree, others: List<TaintTree>): TaintTree? {
        val ordinary = subtract(t.root, t, others, protectedOnly = false)
        // Ordinary ANY coverage cannot consume a fresh protected EXACT dependency.
        val protection = t.nonSubsumable?.let { subtract(it, t, others, protectedOnly = true) }
        val root = mergeProtection(ordinary, protection) ?: return null
        if (root === t.root && protection === t.nonSubsumable) return t
        return admittedTree(m, t, root, protection)
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

    fun add(f: Facts): Facts? = addAll(f).also {
        check(it.size <= 1) { "Canonical admission has multiple headers; use addAll" }
    }.singleOrNull()

    fun addAll(f: Facts): List<Facts> {
        m.cancellation.checkpoint()
        return when (f) {
            is Reach -> if (reach[f.layer.ordinal]) emptyList() else listOf(f.also { reach[f.layer.ordinal] = true })
            is FlowTree -> flow.getOrPut(f.base) { FlowGroup(m, interners.flow) }.addAll(f)
            is TaintTree -> taint.getOrPut(f.base) { TaintGroup(m, interners.taint) }.addAll(f)
        }
    }

    fun retainCurrent(offered: Facts): List<Facts> = retainCurrentFacts(m,offered,all().asIterable())

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
