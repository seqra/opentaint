package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import java.util.ArrayDeque

/** A path filter runs before the concrete mark policy; the input annotations belong to the whole tails. */
internal fun filterFacts(m: ApManager, c: Facts, f: TypeFilter): Facts? {
    m.cancellation.checkpoint()
    return when (c) {
        is Reach -> c
        is FlowTree -> FlowAlgebra.filterPath(m, c.root, f.may)
            ?.let { if (it === c.root) c else c.withRoot(it) }
        is TaintTree -> {
            var result = m.taintAlg.filterPath(m, c.root, f.may)
            val policy = f.markPolicy
            if (result != null && policy != null) result = markPolicy(m, result, policy)
            result?.let { if (it === c.root) c else m.taintTree(c.base, c.layer, it, c.exclusion, c.anyTail) }
        }
    }
}

private class FilterState<P : TrieLeaf>(val node: TrieNode<P>, val filter: FactTypeChecker.FactApFilter) {
    private val hash = System.identityHashCode(node) * 31 + System.identityHashCode(filter)
    override fun hashCode(): Int = hash
    override fun equals(other: Any?): Boolean = other is FilterState<*> &&
        node === other.node && filter === other.filter
}

private class FilterFrame<P : TrieLeaf>(val state: FilterState<P>) {
    var next = 0
    var waiting: FilterState<P>? = null
    var changed = false
    val accessors = ArrayList<Int>()
    val children = ArrayList<TrieNode<P>>()

    fun add(index: Int, child: TrieNode<P>?) {
        val node = state.node
        if (child !== node.childData!![index]) changed = true
        if (child != null) {
            accessors += node.accessorData!![index]
            children += child
        }
    }
}

/** Evaluate each edge once per node/filter identity pair, caching removed subtrees as null. */
internal fun <P : TrieLeaf> LeafAlgebra<P>.filterPath(
    m: ApManager, n: TrieNode<P>, may: FactTypeChecker.FactApFilter,
): TrieNode<P>? {
    m.cancellation.checkpoint()
    val initial = FilterState(n, may)
    val memo = HashMap<FilterState<P>, TrieNode<P>?>()
    val pending = ArrayDeque<FilterFrame<P>>()
    pending.addLast(FilterFrame(initial))
    while (pending.isNotEmpty()) {
        m.cancellation.checkpoint()
        val frame = pending.peekLast()
        val waiting = frame.waiting
        if (waiting != null) {
            check(memo.containsKey(waiting))
            frame.add(frame.next - 1, memo[waiting])
            frame.waiting = null
            continue
        }
        val current = frame.state.node
        val accessors = current.accessorData
        if (accessors != null && frame.next < accessors.size) {
            val index = frame.next++
            val child = current.childData!![index]
            val result = frame.state.filter.check(m.accessors.accessor(accessors[index]))
            m.cancellation.checkpoint()
            when (result) {
                FactTypeChecker.FilterResult.Accept -> frame.add(index, child)
                FactTypeChecker.FilterResult.Reject -> frame.add(index, null)
                is FactTypeChecker.FilterResult.FilterNext -> {
                    val state = FilterState(child, result.filter)
                    if (memo.containsKey(state)) frame.add(index, memo[state])
                    else {
                        frame.waiting = state
                        pending.addLast(FilterFrame(state))
                    }
                }
            }
            continue
        }
        memo[frame.state] = if (!frame.changed) current.takeIf { !it.isEmpty }
            else node(current.leaf, frame.accessors.toIntArray(), frame.children.toTypedArray()).takeIf { !it.isEmpty }
        pending.removeLast()
    }
    return memo[initial]
}

private class PolicyFrame(val node: TaintNode, val kept: TaintLeaves)

/** G6 drop form (spec/acyclic-convergence-proposal.md §5.1). The root and the element spine are filtered by `keeps`, as
 *  in [markPolicyOnSpine]. In addition, at a boxed spine level k (`policy.boxedLevel(k)`), a mark with
 *  `policy.dropsValue(mark, k)` is dropped on the whole value at `[e]^k`: on every leaf of the field subtrees of `[e]^k`
 *  (for example `[e]^k.value`), of each deeper spine node, and on the deeper spine leaves. So at or below a boxed level
 *  the decision for a mark does not depend on the path: an exact fact `x.[e]^k.p` loses the mark if and only if each
 *  cut form `x.[e]^k.q.[any]` (q a prefix of p) loses it (prefix-closed, ap.md S5). Above the first boxed level the
 *  result is that of [markPolicyOnSpine]. Both layers. Proofs: spec/lean/proposals/acyclic-group-a-20261124. */
private fun markPolicy(m: ApManager, n: TaintNode, policy: MarkPolicy): TaintNode? {
    val spine = ArrayList<TaintNode>()
    var current = n
    while (true) {
        m.cancellation.checkpoint()
        spine += current
        current = current.child(ELEMENT_ACCESSOR_IDX) ?: break
    }
    val firstBoxed = spine.indices.firstOrNull { policy.boxedLevel(it) } ?: return markPolicyOnSpine(m, n, policy)
    // droppedAt[j]: the marks of the subtree at the first boxed level that a boxed level k, firstBoxed <= k <= j, drops.
    val candidates = m.taintAlg.foldAll(spine[firstBoxed], m.cancellation).let { it.exact + it.any }
    val droppedAt = arrayOfNulls<MarkSet>(spine.size)
    var dropped = MarkSet.EMPTY
    for (j in spine.indices) {
        m.cancellation.checkpoint()
        if (j >= firstBoxed && policy.boxedLevel(j)) {
            val ids = ArrayList<Int>()
            for (id in candidates.data) if (TaintMark(id) !in dropped && policy.dropsValue(TaintMark(id), j)) ids += id
            if (ids.isNotEmpty()) dropped = m.intern(dropped + MarkSet(ids.toIntArray()))
        }
        droppedAt[j] = dropped
    }
    // Rebuild from the deepest spine node: the spine leaf keeps the `keeps` marks minus droppedAt[j]; the element child
    // is the rebuilt deeper node; every other child loses droppedAt[j] on all its leaves.
    var below: TaintNode? = null
    for (j in spine.indices.reversed()) {
        m.cancellation.checkpoint()
        val node = spine[j]
        val d = droppedAt[j]!!
        val leaf = m.taintLeaves(withoutMarks(keepPolicyMarks(m, node.leaf.exact, policy, j), d),
            withoutMarks(keepPolicyMarks(m, node.leaf.any, policy, j), d))
        val element = below
        below = m.taintAlg.mapChildren(node, leaf, m.cancellation) { accessor, child ->
            when {
                accessor == ELEMENT_ACCESSOR_IDX -> element
                d.isEmpty -> child
                else -> dropOnValue(m, child, d)
            }
        }
    }
    return below
}

private fun withoutMarks(marks: MarkSet, d: MarkSet): MarkSet =
    if (d.isEmpty || marks.data.none { TaintMark(it) in d }) marks else marks - d

/** G6 drop form: drop the marks [d] on every leaf of the subtree [n] (a field subtree below a boxed level). */
private fun dropOnValue(m: ApManager, n: TaintNode, d: MarkSet): TaintNode? {
    val all = m.taintAlg.foldAll(n, m.cancellation)
    if (all.exact.data.none { TaintMark(it) in d } && all.any.data.none { TaintMark(it) in d }) return n
    return m.taintAlg.mapLeaves(n, m.cancellation) { leaf ->
        val e = withoutMarks(leaf.exact, d)
        val a = withoutMarks(leaf.any, d)
        if (e === leaf.exact && a === leaf.any) leaf else m.taintLeaves(e, a)
    }
}

/** The policy for a fact with no boxed level on its element spine: only the root and its uninterrupted element chain
 *  have their payload marks filtered. Here this equals the drop form. */
private fun markPolicyOnSpine(m: ApManager, n: TaintNode, policy: MarkPolicy): TaintNode? {
    val spine = ArrayList<PolicyFrame>()
    var current = n
    var level = 0
    while (true) {
        m.cancellation.checkpoint()
        val kept = m.taintLeaves(keepPolicyMarks(m, current.leaf.exact, policy, level),
            keepPolicyMarks(m, current.leaf.any, policy, level))
        spine += PolicyFrame(current, kept)
        val child = current.child(ELEMENT_ACCESSOR_IDX) ?: break
        current = child
        level = Math.addExact(level, 1)
    }
    var below: TaintNode? = null
    for (index in spine.indices.reversed()) {
        m.cancellation.checkpoint()
        val frame = spine[index]
        val oldChild = frame.node.child(ELEMENT_ACCESSOR_IDX)
        below = when {
            frame.kept === frame.node.leaf && below === oldChild -> frame.node
            oldChild == null -> m.taintAlg.withLeaf(frame.node, frame.kept)
            else -> m.taintAlg.replaceChild(frame.node, frame.kept, ELEMENT_ACCESSOR_IDX, below)
        }
    }
    return below
}

private fun keepPolicyMarks(m: ApManager, marks: MarkSet, policy: MarkPolicy, level: Int): MarkSet {
    if (marks.isEmpty) return marks
    val kept = ArrayList<Int>()
    for (id in marks.data) {
        m.cancellation.checkpoint()
        val atom = TaintMark(id)
        val keep = policy.keeps(atom, level)
        m.cancellation.checkpoint()
        if (keep) kept += id
    }
    return if (kept.size == marks.data.size) marks else m.intern(MarkSet(kept.toIntArray()))
}
