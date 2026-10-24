package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import java.util.ArrayDeque

/** Only the proved canonical run-1 FULL cell has a cross-mark FLOW key.
 * The owner must also match method, point/exit, call stage and effect class. */
fun flowInitialForCoverage(m: ApManager, premise: PremiseKey): InitialAp? {
    m.cancellation.checkpoint()
    val initial = premise as? InitialAp ?: return null
    val mark = initial.mark as? MarkSlot.Concrete ?: return null
    if (initial.manager !== m || initial.isZero || mark.mark == TaintMark.ZERO || initial.tail != Tail.STAR ||
        initial.exclusion != ExclusionSet.Empty || m.marks.isGroup(mark.mark)) return null
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

/** Remove only plain diagonal ANY memberships covered by the supplied FLOW
 * trees. The owner has already checked scope, initial key, handoff and alias
 * effect compatibility. EXACT/MUST, cross-mark and protected parts remain.
 *
 * Each candidate tree is joined with the TAINT trie along matching branches.
 * There is no enumeration of FLOW paths or FLOW-path × TAINT-path product.
 * Protection is an explicit input, since ordinary fact equality ignores it. */
fun removeFlowCoveredAny(m: ApManager, initial: PremiseKey, facts: TaintTree,
                         flow: Iterable<FlowTree>, protection: TaintNode? = null): TaintTree? {
    m.cancellation.checkpoint()
    if (facts.anyTail != Tail.ANY || flowInitialForCoverage(m, initial) == null) return facts
    val mark = ((initial as InitialAp).mark as MarkSlot.Concrete).mark
    var root: TaintNode = facts.root
    for (candidate in flow) {
        m.cancellation.checkpoint()
        if (!eligibleAnyHeader(candidate, facts.base, mark, facts.layer)) continue
        root = removeCoveredDiagonal(m, root, candidate.root, protection, mark) ?: return null
    }
    return if (root === facts.root) facts else facts.withRoot(root)
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
