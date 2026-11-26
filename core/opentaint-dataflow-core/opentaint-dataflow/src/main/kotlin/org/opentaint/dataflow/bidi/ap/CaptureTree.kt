package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.ir.api.common.cfg.CommonInst

/**
 * One field tree per (place, rule occurrence, `[any]` literal) (spec backward-condition-progress §I.3).
 * [rule] is a `RuleOccurrenceId` (predicate sinks and conditional sources) or the legacy sink rule.
 */
data class CaptureKey(val method: MethodKey, val statement: CommonInst, val rule: Any, val literal: Pattern)

/**
 * Lean `BackND.insertLeaf` on a trie below the literal path. Returns the same object if nothing changes.
 *
 * - an `[any]` leaf at a prefix of [sigma] (σ included): no change;
 * - a `$` leaf and a `$` leaf at σ: no change;
 * - an `[any]` leaf: the subtree at σ becomes one `[any]` leaf;
 * - a `$` leaf: a `$` leaf at σ; the leaves below σ stay.
 */
internal fun TaintAlgebra.insertCaptureLeaf(root: TaintNode?, sigma: IntArray, any: Boolean,
                                            exactLeaf: TaintLeaves, anyLeaf: TaintLeaves): TaintNode {
    fun go(n: TaintNode?, d: Int): TaintNode? {                       // null: no change
        if (n != null && n.leaf.hasAny) return null
        if (d == sigma.size) return when {
            any -> leafNode(anyLeaf)
            n != null && !n.leaf.isEmpty -> null
            else -> node(exactLeaf, n?.accessorData, n?.childData)
        }
        val child = go(n?.child(sigma[d]), d + 1) ?: return null
        return replaceChild(n, n?.leaf ?: empty, sigma[d], child)
    }
    return go(root, 0) ?: checkNotNull(root)
}

/** One leaf below the literal path, with the literal mark (C10). */
internal fun ApManager.captureLeaf(tree: TaintNode?, sigma: IntArray, any: Boolean, literal: Pattern): TaintNode {
    val mark = MarkSet.EMPTY + (literal.fact.mark as MarkSlot.Concrete).mark
    return taintAlg.insertCaptureLeaf(tree, sigma, any, taintAlg.leaves(mark, MarkSet.EMPTY), taintAlg.leaves(MarkSet.EMPTY, mark))
}

/**
 * Meet first, then the normal form (spec §I.3): insert the leaves of one checked input. The checked piece is the
 * overlap with the literal (`checkMark`), so the two "no overlap" returns add no leaf.
 */
internal fun ApManager.captureInput(tree: TaintNode?, input: TaintTree, literal: Pattern): TaintNode? {
    var result = tree
    var n: TaintNode? = input.root
    for (accessor in literal.fact.path) {
        cancellation.checkpoint()
        val node = n ?: return result                                                // no overlap: no leaf
        if (node.leaf.hasAny && input.exclusion.admits(accessor))
            return captureLeaf(result, EMPTY_PATH, any = true, literal)              // meet: input above -> the literal
        n = node.child(accessor)
    }
    val tip = n ?: return result                                                     // no overlap: no leaf
    taintAlg.forEachLeaf(tip, EMPTY_PATH, cancellation) { sigma, leaf ->              // meet: input at or below
        if (!leaf.isEmpty) result = captureLeaf(result, sigma, leaf.hasAny, literal)
    }
    return result
}

/** The refined seed (spec §II.4): the literal fact with the tree below the literal path, DEMAND (C10). */
internal fun ApManager.treeSeed(literal: TaintTree, literalPath: List<AccessorIdx>, tree: TaintNode): TaintTree {
    val marks = taintAlg.foldAll(literal.root, cancellation).any                       // the literal mark of this run
    val exact = taintAlg.leaves(marks, MarkSet.EMPTY)
    val any = taintAlg.leaves(MarkSet.EMPTY, marks)
    val body = checkNotNull(taintAlg.mapLeaves(tree, cancellation) { l ->
        when { l.isEmpty -> l; l.hasAny -> any; else -> exact } })
    return taintTree(literal.base, Layer.DEMAND, taintAlg.prepend(this, path(literalPath), body), anyTail = Tail.ANY)
}

/** Merge two trees of one key (two analyzers of one method): insert each leaf of [b] into [a]. */
internal fun ApManager.mergeCapture(a: TaintNode, b: TaintNode, literal: Pattern): TaintNode {
    var result = a
    taintAlg.forEachLeaf(b, EMPTY_PATH, cancellation) { sigma, leaf ->
        if (!leaf.isEmpty) result = captureLeaf(result, sigma, leaf.hasAny, literal)
    }
    return result
}
