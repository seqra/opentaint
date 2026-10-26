package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import java.util.ArrayDeque

/** The owner fixes method, run, view and summary endpoint. Preserve all
 * admitted counterpart geometry; no runtime atom or iteration gate applies. */
fun flowInitialForCoverage(m: ApManager, premise: PremiseKey): InitialAp? {
    m.cancellation.checkpoint()
    val initial = premise as? InitialAp ?: return null
    val mark = initial.mark as? MarkSlot.Concrete ?: return null
    if (initial.manager !== m || initial.isZero || mark.mark == TaintMark.ZERO || (initial.tail != Tail.STAR && initial.tail != Tail.ANY)) return null
    return m.initial(initial.base, initial.path, initial.tail, initial.exclusion, MarkSlot.STAR)
}

private fun eligibleAnyHeader(flow: FlowTree, base: AccessPathBase, mark: TaintMark, layer: Layer): Boolean =
    flow.base == base && flow.tail == Tail.ANY && mark !in flow.markExclusion &&
        (flow.layer == Layer.NORMAL || layer == Layer.DEMAND)

/** Look only along the one TAINT path. A branch without a FLOW leaf is not
 * an output. All header gates apply to the same selected FLOW output. */
fun flowCoversAny(m: ApManager, flow: FlowTree, base: AccessPathBase, path: IntArray,
                  mark: TaintMark, layer: Layer): Boolean {
    m.cancellation.checkpoint()
    if (!eligibleAnyHeader(flow, base, mark, layer)) return false
    var node = flow.root
    if (!node.leaf.isEmpty) return true
    for (accessor in path) {
        m.cancellation.checkpoint()
        node = node.child(accessor) ?: return false
        if (!node.leaf.isEmpty) return true
    }
    return false
}

/** Remove plain diagonal memberships under one complete FLOW candidate.
 * STAR uses equal output paths and suffix-exclusion inclusion; ANY uses
 * prefixes. EXACT/must, cross-atom and protected memberships remain. */
fun removeFlowCovered(m: ApManager, initial: PremiseKey, facts: TaintTree,
                      flow: Iterable<FlowTree>, protection: TaintNode? = null): TaintTree? {
    m.cancellation.checkpoint()
    if ((facts.anyTail != Tail.STAR && facts.anyTail != Tail.ANY) || flowInitialForCoverage(m, initial) == null) return facts
    val mark = ((initial as InitialAp).mark as MarkSlot.Concrete).mark
    var root: TaintNode = facts.root
    for (candidate in flow) {
        m.cancellation.checkpoint()
        if (candidate.base != facts.base || candidate.tail != facts.anyTail || mark in candidate.markExclusion ||
            (candidate.layer != Layer.NORMAL && facts.layer != Layer.DEMAND) ||
            (facts.anyTail == Tail.STAR && !candidate.exclusion.isSubsetOf(facts.exclusion))) continue
        root = if (facts.anyTail == Tail.STAR)
            removeCoveredStar(m, root, candidate.root, protection, mark) ?: return null
        else removeCoveredDiagonal(m, root, candidate.root, protection, mark) ?: return null
    }
    return if (root === facts.root) facts else facts.withRoot(root)
}

/** Compatibility entry for callers which explicitly inspect the ANY cell. */
fun removeFlowCoveredAny(m: ApManager, initial: PremiseKey, facts: TaintTree,
                         flow: Iterable<FlowTree>, protection: TaintNode? = null): TaintTree? =
    if (facts.anyTail == Tail.ANY) removeFlowCovered(m, initial, facts, flow, protection) else facts

private class StarCoverKey(val taint: TaintNode, val flow: FlowNode?, val protected: TaintNode?) {
    override fun hashCode(): Int = (System.identityHashCode(taint) * 31 + System.identityHashCode(flow)) * 31 +
        System.identityHashCode(protected)
    override fun equals(other: Any?): Boolean = other is StarCoverKey && taint === other.taint &&
        flow === other.flow && protected === other.protected
}
private class StarCoverFrame(val key: StarCoverKey, var expanded: Boolean = false)

/** Equal-node walk: an annotated proper prefix cannot cover a shared suffix. */
private fun removeCoveredStar(m: ApManager, root: TaintNode, flow: FlowNode,
                              protection: TaintNode?, mark: TaintMark): TaintNode? {
    val memo = HashMap<StarCoverKey, TaintNode?>()
    val stack = ArrayDeque<StarCoverFrame>()
    val initial = StarCoverKey(root, flow, protection)
    val one = m.markSetOf(mark)
    stack.addLast(StarCoverFrame(initial))
    while (stack.isNotEmpty()) {
        m.cancellation.checkpoint()
        val frame = stack.peekLast()
        val key = frame.key
        if (memo.containsKey(key)) { stack.removeLast(); continue }
        if (key.flow == null) { memo[key] = key.taint; stack.removeLast(); continue }
        fun childKey(accessor: Int, child: TaintNode) =
            StarCoverKey(child, key.flow.child(accessor), key.protected?.child(accessor))
        if (!frame.expanded) {
            frame.expanded = true
            key.taint.accessorData?.forEachIndexed { i, accessor ->
                val child = childKey(accessor, key.taint.childData!![i])
                if (!memo.containsKey(child)) stack.addLast(StarCoverFrame(child))
            }
            continue
        }
        val leaf = key.taint.leaf
        val remove = key.flow.leaf == FlowLeaf.LEAF && key.protected?.leaf?.any?.contains(mark) != true
        val remaining = if (remove) m.taintLeaves(leaf.exact, leaf.any - one) else leaf
        memo[key] = m.taintAlg.mapChildren(key.taint, remaining, m.cancellation) { accessor, child ->
            memo.getValue(childKey(accessor, child))
        }
        stack.removeLast()
    }
    return memo.getValue(initial)
}

/** References are deliberate: structural trie hashing here would traverse
 * shared geometry while building the traversal memo. */
private class AnyCoverKey(val taint: TaintNode, val flow: FlowNode?, val protected: TaintNode?,
                          val coveredAbove: Boolean, val protectedAbove: Boolean) {
    override fun hashCode(): Int = (((System.identityHashCode(taint) * 31 + System.identityHashCode(flow)) * 31 +
        System.identityHashCode(protected)) * 31 + coveredAbove.hashCode()) * 31 + protectedAbove.hashCode()
    override fun equals(other: Any?): Boolean = other is AnyCoverKey && taint === other.taint &&
        flow === other.flow && protected === other.protected && coveredAbove == other.coveredAbove &&
        protectedAbove == other.protectedAbove
}

private class AnyCoverFrame(val key: AnyCoverKey, var expanded: Boolean = false)

private fun removeCoveredDiagonal(m: ApManager, root: TaintNode, flow: FlowNode,
                                   protection: TaintNode?, mark: TaintMark): TaintNode? {
    val alg = m.taintAlg
    val memo = HashMap<AnyCoverKey, TaintNode?>()
    val stack = ArrayDeque<AnyCoverFrame>()
    val initial = AnyCoverKey(root, flow, protection, coveredAbove = false, protectedAbove = false)
    val one = m.markSetOf(mark)
    stack.addLast(AnyCoverFrame(initial))
    while (stack.isNotEmpty()) {
        m.cancellation.checkpoint()
        val frame = stack.peekLast()
        val key = frame.key
        if (memo.containsKey(key)) {
            stack.removeLast()
            continue
        }
        if ((!key.coveredAbove && key.flow == null) || mark !in alg.foldAll(key.taint, m.cancellation).any) {
            memo[key] = key.taint
            stack.removeLast()
            continue
        }
        val coveredHere = key.coveredAbove || key.flow?.leaf == FlowLeaf.LEAF
        val protectedHere = key.protectedAbove || key.protected?.leaf?.any?.contains(mark) == true
        fun childKey(accessor: Int, child: TaintNode) = AnyCoverKey(child,
            if (coveredHere) null else key.flow?.child(accessor), key.protected?.child(accessor),
            coveredHere, protectedHere)
        if (!frame.expanded) {
            frame.expanded = true
            key.taint.accessorData?.forEachIndexed { i, accessor ->
                m.cancellation.checkpoint()
                val child = childKey(accessor, key.taint.childData!![i])
                if (!memo.containsKey(child)) stack.addLast(AnyCoverFrame(child))
            }
            continue
        }
        // An ANY membership contains descendant EXACT protection too. Keep
        // that wider marked member rather than lose the protected subregion.
        val protectedBelow = key.protected?.let { alg.foldAll(it, m.cancellation) }
            ?.let { mark in it.exact || mark in it.any } == true
        val leaf = key.taint.leaf
        val offered = if (coveredHere && !protectedHere && !protectedBelow && mark in leaf.any)
            m.taintLeaves(leaf.exact, leaf.any - one) else leaf
        memo[key] = alg.mapChildren(key.taint, offered, m.cancellation) { accessor, child ->
            memo.getValue(childKey(accessor, child))
        }
        stack.removeLast()
    }
    return memo.getValue(initial)
}
