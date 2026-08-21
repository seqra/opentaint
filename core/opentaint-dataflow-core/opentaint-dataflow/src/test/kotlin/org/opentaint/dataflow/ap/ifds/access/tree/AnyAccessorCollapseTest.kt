package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.createNodeFromAccessors
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.createAbstractNodeFromAccessors
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

/**
 * The representation invariant around `[any]`: no `[any]` is reachable from another `[any]` through
 * a covered-only path, and `[any]`'s cost charge on `maxDepth` is a cost, not a sentinel.
 *
 * `[any]` denotes ZERO OR MORE covered steps, so `[any].x.y.z.[any].S` and `[any].S` denote the same
 * path set whenever `x`, `y`, `z` are covered -- the collapse is an identity, not an approximation.
 * The identity does not hold across an accessor `[any]` does not cover, so the collapse stops there.
 */
class AnyAccessorCollapseTest {

    private companion object {
        val FIELD_X = FieldAccessor("Box", "x", "Box")
        val FIELD_Y = FieldAccessor("Box", "y", "Box")
        val FIELD_Z = FieldAccessor("Box", "z", "Box")

        val TYPE = TypeInfoAccessor("Box")
        val MARK = TaintMarkAccessor("m")
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())

    private val base = AccessPathBase.This

    private fun idx(accessor: Accessor) = with(manager) { accessor.idx }

    private fun concreteFact(vararg accessors: Accessor): AccessTree {
        var fact = manager.createFinalAp(base, ExclusionSet.Empty)
        for (accessor in accessors.reversed()) {
            fact = fact.prependAccessor(accessor)
        }
        return fact as AccessTree
    }

    private fun treeOf(node: AccessNode) = AccessTree(manager, base, node, ExclusionSet.Empty)

    /** Raw node construction, bypassing [AccessTree.prependAccessor] so illegal shapes stay illegal. */
    private fun node(isAbstract: Boolean, isFinal: Boolean, vararg children: Pair<Accessor, AccessNode>): AccessNode {
        val sorted = children.map { idx(it.first) to it.second }.sortedBy { it.first }
        return manager.create(
            isAbstract, isFinal, null,
            sorted.map { it.first }.toIntArray(),
            sorted.map { it.second }.toTypedArray(),
        )
    }

    private fun node(vararg children: Pair<Accessor, AccessNode>): AccessNode =
        node(isAbstract = false, isFinal = false, children = children)

    private fun premiseChain(length: Int): AccessPath.AccessNode {
        val accessors = IntArrayList()
        repeat(length) { accessors.add(idx(FieldAccessor("Chain", "f$it", "Chain"))) }
        return manager.createNodeFromAccessors(accessors)!!
    }

    /* ---------- the deep flag ---------- */

    @Test
    fun `containsAnyInThisOrDeepNodes is deep where containsAnyAccessor is shallow`() {
        val deep = concreteFact(FIELD_X, FIELD_Y, FIELD_Z, AnyAccessor).access // this.x.y.z.[any].$

        assertTrue(deep.containsAnyInThisOrDeepNodes, "an [any] three levels down is still in reach")
        assertFalse(deep.containsAnyAccessor(), "the shallow counterpart tests THIS NODE only")

        val plain = concreteFact(FIELD_X, FIELD_Y, FIELD_Z).access
        assertFalse(plain.containsAnyInThisOrDeepNodes, "an [any]-free tree must keep the flag clear")
    }

    /* ---------- the collapse ---------- */

    @Test
    fun `prepending any onto a direct any child yields a single any`() {
        // the pre-existing one-level behaviour, pinned
        val fact = concreteFact(AnyAccessor) // this.[any].$
        val prepended = fact.prependAccessor(AnyAccessor) as AccessTree

        assertEquals(fact.access, prepended.access, "[any].[any].S == [any].S")
        assertEquals(listOf(ANY_ACCESSOR_IDX), prepended.access.accessors!!.toList())
        assertFalse(
            prepended.access.accessorNodes!!.single().containsAnyInThisOrDeepNodes,
            "no [any] may remain below the new [any]"
        )
    }

    @Test
    fun `prepending any collapses an any reachable through covered accessors`() {
        val fact = concreteFact(FIELD_X, FIELD_Y, AnyAccessor) // this.x.y.[any].$
        val prepended = fact.prependAccessor(AnyAccessor) as AccessTree

        assertEquals(concreteFact(AnyAccessor).access, prepended.access, "[any].x.y.[any].S == [any].S")
        assertEquals(listOf(ANY_ACCESSOR_IDX), prepended.access.accessors!!.toList())
        assertFalse(
            prepended.access.accessorNodes!!.single().containsAnyInThisOrDeepNodes,
            "no [any] may remain below the new [any]"
        )

        // and it still answers the same reads as the uncollapsed shape it replaced
        val uncollapsed = treeOf(node(AnyAccessor to fact.access)) // [any].x.y.[any].$, built raw
        for (accessor in listOf(FIELD_X, FIELD_Y, FIELD_Z, ElementAccessor, TYPE)) {
            assertEquals(
                uncollapsed.startsWithAccessor(accessor),
                prepended.startsWithAccessor(accessor),
                "startsWith($accessor) must be unchanged by the collapse"
            )
            assertEquals(
                uncollapsed.readAccessor(accessor) != null,
                prepended.readAccessor(accessor) != null,
                "read of $accessor must be unchanged by the collapse"
            )
        }
    }

    @Test
    fun `prepending any does not collapse an any below an uncovered accessor`() {
        val fact = concreteFact(TYPE, AnyAccessor) // this.{Box}.[any].$ -- {Box} is not covered by [any]
        val prepended = fact.prependAccessor(AnyAccessor) as AccessTree

        assertEquals(listOf(ANY_ACCESSOR_IDX), prepended.access.accessors!!.toList())

        val belowNewAny = prepended.access.accessorNodes!!.single()
        assertTrue(belowNewAny.containsAnyInThisOrDeepNodes, "the [any] below {Box} must survive")
        assertEquals(fact.access, belowNewAny, "nothing below an uncovered accessor may be rewritten")
    }

    /* ---------- no [any] below a taint mark ---------- */

    @Test
    fun `a taint mark may not be built above a structured node`() {
        val accessors = IntArrayList().apply {
            add(idx(MARK))
            add(idx(FIELD_X))
        }

        assertFailsWith<IllegalStateException>("![m].x is not a legal shape") {
            manager.createAbstractNodeFromAccessors(accessors)
        }
    }

    /* ---------- the suffix matcher ---------- */

    @Test
    fun `the any suffix matcher absorbs a nested any instead of aborting`() {
        // the node hanging under an outer [any] edge: x.($ + [any].y.$)
        // i.e. the outer suffix language is [any].x.[any].y.$ (and [any].x.$)
        val suffix = node(FIELD_X to node(isAbstract = false, isFinal = true, AnyAccessor to node(FIELD_Y to manager.finalNode)))

        val matcher = AccessTreeAnySuffixMatcher(suffix)

        // x.y.$ is reached through the ABSORBED nested [any]: it must be trimmed away entirely
        val covered = node(FIELD_X to node(FIELD_Y to manager.finalNode))
        assertTrue(
            matcher.getNonMatchingNode(covered).isEmpty,
            "the outer [any] covers x.y.\$ through the absorbed nested [any]"
        )

        // a branch the suffix does not reach must survive untouched
        val outside = node(FIELD_Z to manager.finalNode)
        assertEquals(outside, matcher.getNonMatchingNode(outside), "z.\$ is outside the suffix language")
    }

    /* ---------- the maxDepth prefilter ---------- */

    @Test
    fun `filterStartsWith matches a premise longer than the any depth charge`() {
        val fact = node(AnyAccessor to manager.abstractNode) // base.[any].*

        assertEquals(11, fact.maxDepth, "one step plus the [any] cost charge")

        val chain = premiseChain(16)
        assertTrue(chain.size > fact.maxDepth, "the premise must outrun the charged depth")

        // getChild synthesises children through the [any] edge to arbitrary depth, so the maxDepth
        // prefilter must not fire here -- doing so would lose the flow.
        assertNotNull(fact.filterStartsWith(chain), "an [any] fact reaches an arbitrarily long premise")

        // ... while the prefilter stays active where maxDepth really does bound the descent
        val boundedFact = node(FIELD_X to manager.abstractNode)
        assertEquals(1, boundedFact.maxDepth)
        assertEquals(null, boundedFact.filterStartsWith(chain), "no [any]: the prefilter still prunes")
    }
}
