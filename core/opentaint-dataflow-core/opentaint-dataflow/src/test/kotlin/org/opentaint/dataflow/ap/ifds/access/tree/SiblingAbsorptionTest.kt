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
import kotlin.test.assertFalse
import kotlin.test.assertSame
import kotlin.test.assertTrue

/**
 * `N{ f -> T , [any] -> S }  ==>  N{ [any] -> (S | T) }` for covered `f`.
 *
 * The operation ABSORBS rather than deletes, and that is the whole point. Deleting a subsumed
 * sibling is exact and still costs every finding, because the branch's contents are the names
 * `TreeInitialFactAbstraction` emits premises from. Merging the subtree into the `[any]` keeps
 * them AND moves them one level under the `[any]`, which is where R3b looks.
 */
class SiblingAbsorptionTest {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation(), -1)
    private val base = AccessPathBase.This

    private val F = FieldAccessor("N", "f", "N")
    private val G = FieldAccessor("N", "g", "N")
    private val MARK = TaintMarkAccessor("test-mark")

    /** `<accessors>.*` -- open at the leaf, the production shape. */
    private fun open(vararg accessors: Accessor): AccessTree.AccessNode {
        var f: FinalFactAp = manager.mostAbstractFinalAp(base)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return (f as AccessTree).access
    }

    private fun node(vararg branches: AccessTree.AccessNode): AccessTree.AccessNode {
        var n = manager.emptyNode
        branches.forEach { n = n.mergeAdd(it) }
        return n
    }

    private fun AccessTree.AccessNode.render(): String =
        toString().replace('\n', ' ').trim()

    private fun idx(a: Accessor): Int = with(manager) { a.idx }

    @Test
    fun `a covered sibling is folded into the any`() {
        val n = node(open(F, G), open(AnyAccessor))          // { f.g.* , [any].* }
        assertTrue(n.contains(idx(F)), "precondition: the f edge is there")

        val c = n.compressAbsorbCoveredSiblings()

        assertFalse(
            c.accessors!!.contains(idx(F)),
            "the covered `f` EDGE must be gone -- it is denoted by the [any]; got ${c.render()}",
        )
        assertTrue(c.accessors!!.contains(idx(AnyAccessor).let { it }), "the [any] survives")
    }

    /**
     * The reason to absorb rather than delete. A mark buried under a covered sibling ends up
     * DIRECTLY below the `[any]`, which is the one place R3b enumerates.
     */
    @Test
    fun `a mark under a covered sibling is hoisted to directly under the any`() {
        val n = node(open(F, MARK), open(AnyAccessor))       // { f.![m].* , [any].* }

        val c = n.compressAbsorbCoveredSiblings()

        assertFalse(c.accessors!!.contains(idx(F)), "the `f` edge is absorbed")
        val anyChild = c.getChildForTest(idx(AnyAccessor))
        assertTrue(anyChild != null, "the [any] subtree survives")
        assertTrue(
            anyChild!!.accessors!!.contains(idx(MARK)),
            "the mark must now sit ONE level under the [any], where R3b enumerates; got ${c.render()}",
        )
    }

    @Test
    fun `an uncovered sibling is never absorbed`() {
        val n = node(open(MARK), open(AnyAccessor))          // { ![m].* , [any].* }

        val c = n.compressAbsorbCoveredSiblings()

        assertTrue(
            c.accessors!!.contains(idx(MARK)),
            "a taint mark is not denoted by [any] and must stay a literal edge; got ${c.render()}",
        )
    }

    @Test
    fun `without an any nothing moves, by identity`() {
        val n = node(open(F, G), open(G))
        assertSame(n, n.compressAbsorbCoveredSiblings(), "no [any] here, so nothing to absorb into")
    }

    /**
     * Idempotence BY IDENTITY, which the storage layer requires: every storage decides "already
     * known" with `merged === stored`, so a pass that rebuilt an unchanged node would make every
     * re-derivation look new and re-propagate the whole tree.
     */
    @Test
    fun `the pass is idempotent by identity`() {
        val n = node(open(F, G), open(AnyAccessor), open(MARK))
        val once = n.compressAbsorbCoveredSiblings()
        val twice = once.compressAbsorbCoveredSiblings()
        assertSame(once, twice, "a second pass must return the very same object; got ${twice.render()}")
    }
}
