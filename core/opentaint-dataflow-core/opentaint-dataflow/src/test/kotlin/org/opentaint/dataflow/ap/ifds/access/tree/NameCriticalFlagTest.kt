package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * `containsNameCriticalInThisOrDeepNodes` is the O(1) bit the self-subsumption census crosses its
 * classification with, so a wrong bit would silently turn "none of the redundant mass is
 * name-critical" into a false result. Pin it directly.
 */
class NameCriticalFlagTest {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation(), -1)
    private val base = AccessPathBase.This

    private val F = FieldAccessor("N", "f", "N")
    private val G = FieldAccessor("N", "g", "N")
    private val MARK = TaintMarkAccessor("test-mark")

    private fun fact(vararg accessors: Accessor): FinalFactAp {
        var f = manager.createFinalAp(base, ExclusionSet.Empty)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return f
    }

    private fun flag(f: FinalFactAp) = (f as AccessTree).access.containsNameCriticalInThisOrDeepNodes

    @Test
    fun `a purely structural branch is not name-critical`() {
        assertFalse(flag(fact(F, G)), "f.g.$ holds only covered accessors")
        assertFalse(flag(fact(F, AnyAccessor, G)), "an [any] is not name-critical either")
        assertFalse(flag(fact(ElementAccessor, F)), "nor is an element step")
    }

    @Test
    fun `a taint mark makes the branch name-critical at every depth above it`() {
        assertTrue(flag(fact(MARK)), "the mark itself")
        assertTrue(flag(fact(F, MARK)), "one level above")
        assertTrue(flag(fact(F, G, MARK)), "two levels above")
        assertTrue(flag(fact(F, AnyAccessor, MARK)), "and through an [any]")
    }

    @Test
    fun `the bit is a union over siblings, not a property of one path`() {
        val marked = (fact(F, MARK) as AccessTree).access
        val plain = (fact(G, F) as AccessTree).access
        assertFalse(plain.containsNameCriticalInThisOrDeepNodes)
        assertTrue(
            plain.mergeAdd(marked).containsNameCriticalInThisOrDeepNodes,
            "merging a marked branch in must set the bit on the merged root",
        )
    }
}

/**
 * The classifier the self-subsumption census uses, pinned on hand-built shapes.
 *
 * The census reported "100% of siblings fully subsumed, 0 partial, 0 not subsumed" on the frontier
 * arm. That is only believable if the matcher CAN say no, and these tests show it can: the uniform
 * 100% is a property of the FACTS, not of the classifier.
 *
 * Two semantics that are easy to get wrong and that these tests pin:
 *  - an "empty" result is `manager.emptyNode`, whose `size` is **1**, not 0;
 *  - `*` (abstract, "any continuation") does NOT imply `$` (final, "the path ends here"), so
 *    `[any].*` does not subsume a sibling ending in `$`. Production facts end abstract -- the dumps
 *    render `.Element.inputData.[any]` over an abstract leaf -- which is why the residue is total there.
 */
class SelfSubsumptionClassifierTest {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation(), -1)
    private val base = AccessPathBase.This
    private val F = FieldAccessor("N", "f", "N")
    private val G = FieldAccessor("N", "g", "N")
    private val H = FieldAccessor("N", "h", "N")

    /** `<accessors>.*` -- open at the leaf, the shape a production fact has. */
    private fun open(vararg accessors: Accessor): AccessTree.AccessNode {
        var f = manager.mostAbstractFinalAp(base)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return (f as AccessTree).access
    }

    private fun keptSiblings(suffix: AccessTree.AccessNode, vararg siblings: AccessTree.AccessNode): AccessTree.AccessNode {
        var node = manager.emptyNode
        siblings.forEach { node = node.mergeAdd(it) }
        return AccessTreeAnySuffixMatcher(suffix, forceCancelAbstract = true).getNonMatchingNode(node)
    }

    @Test
    fun `an abstract any subtree subsumes every sibling - the production shape`() {
        val kept = keptSiblings(manager.abstractNode, open(F, G), open(H))
        assertTrue(kept.isEmpty, "[any].* denotes every path here, so nothing survives; got $kept")
    }

    @Test
    fun `a concrete any subtree does NOT subsume an unrelated sibling`() {
        val kept = keptSiblings(open(G), open(H))
        assertFalse(kept.isEmpty, "h is not denoted by [any].g -- the classifier must say NO")
        assertTrue(kept.contains(idxOf(H)), "and it must be `h` that survives; got $kept")
    }

    @Test
    fun `a concrete any subtree does subsume the sibling it denotes`() {
        val kept = keptSiblings(open(G), open(F, G))
        assertTrue(
            kept.isEmpty,
            "f.g.* IS denoted by [any].g.* with the [any] taking one covered step; got $kept",
        )
    }

    private fun idxOf(a: Accessor): Int = with(manager) { a.idx }
}
