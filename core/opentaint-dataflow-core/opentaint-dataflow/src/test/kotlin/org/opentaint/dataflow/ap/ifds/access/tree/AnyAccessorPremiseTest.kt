package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.createNodeFromAccessors
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull

/**
 * The premise side of the `[any]` representation: `AccessPath` is a singly-linked accessor CHAIN,
 * and until now `AccessPath.AccessNode.addParent` silently dropped an `[any]` prepended onto a
 * non-empty chain while the empty-chain branch of `prependAccessor` kept it. The two halves
 * disagreed; these tests pin the agreed behaviour.
 *
 * The invariant is the one the fact side maintains (see [AnyAccessorCollapseTest]): no `[any]` is
 * reachable from another `[any]` through a covered-only path. On a chain that means a run of covered
 * accessors ending in an `[any]` collapses into the prepended `[any]`, which under the zero-or-more
 * reading is an identity rather than an approximation. The collapse stops at the first accessor
 * `[any]` does not cover.
 */
class AnyAccessorPremiseTest {

    private companion object {
        val FIELD_X = FieldAccessor("Box", "x", "Box")
        val FIELD_Y = FieldAccessor("Box", "y", "Box")
        val FIELD_Z = FieldAccessor("Box", "z", "Box")
        val FIELD_B = FieldAccessor("Box", "b", "Box")

        val TYPE = TypeInfoAccessor("Box")
        val MARK = TaintMarkAccessor("m")
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    // An EXPLICIT limit. Without one this manager inherits `-Dopentaint.anyUnrollLimit` from the
    // Gradle JVM, which `configureDefaultTest` forwards into the forked test worker AND declares a
    // task input -- so these representation constraints would be silently sensitive to a knob, and a
    // gate run could not tell a regression from a setting. `-1` is the feature off, which is what
    // every assertion in this file is about.
    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation(), -1)

    private val base = AccessPathBase.This

    private fun idx(accessor: Accessor) = with(manager) { accessor.idx }

    /** Raw chain construction, bypassing [AccessPath.prependAccessor] so any shape stays buildable. */
    private fun chain(vararg accessors: Accessor): AccessPath.AccessNode {
        val indices = IntArrayList()
        accessors.forEach { indices.add(idx(it)) }
        return manager.createNodeFromAccessors(indices)!!
    }

    private fun premise(vararg accessors: Accessor): AccessPath =
        AccessPath(manager, base, chain(*accessors), ExclusionSet.Empty)

    private fun AccessPath.AccessNode.accessors(): List<Accessor> = accessorList()

    private fun InitialFactAp.accessors(): List<Accessor> =
        (this as AccessPath).access?.accessorList().orEmpty()

    private fun anyOnto(vararg accessors: Accessor): List<Accessor> =
        chain(*accessors).addParent(idx(AnyAccessor)).accessors()

    /* ---------- 3A: addParent no longer drops `[any]` ---------- */

    @Test
    fun `any prepended onto a covered chain with no inner any is kept as a link`() {
        assertEquals(
            listOf(AnyAccessor, FIELD_X, FIELD_Y, FinalAccessor),
            anyOnto(FIELD_X, FIELD_Y, FinalAccessor),
            "[any] onto x.y.\$ is [any].x.y.\$ -- nothing collapses"
        )
    }

    @Test
    fun `any prepended onto a chain already headed by any collapses to one any`() {
        assertEquals(
            listOf(AnyAccessor, FinalAccessor),
            anyOnto(AnyAccessor, FinalAccessor),
            "[any] onto [any].S is [any].S"
        )

        assertEquals(
            listOf(AnyAccessor, TYPE, FinalAccessor),
            anyOnto(AnyAccessor, TYPE, FinalAccessor),
            "the suffix below the inner [any] is kept verbatim"
        )
    }

    @Test
    fun `any absorbs a covered run ending in an inner any`() {
        assertEquals(
            listOf(AnyAccessor, FinalAccessor),
            anyOnto(FIELD_X, FIELD_Y, AnyAccessor, FinalAccessor),
            "[any] onto x.y.[any].S is [any].S -- x and y are covered, so the collapse is an identity"
        )

        assertEquals(
            listOf(AnyAccessor, FIELD_Z, FinalAccessor),
            anyOnto(FIELD_X, ElementAccessor, AnyAccessor, FIELD_Z, FinalAccessor),
            "everything below the inner [any] survives, elements are covered too"
        )
    }

    @Test
    fun `the scan stops at the first accessor any does not cover`() {
        assertEquals(
            listOf(AnyAccessor, MARK, FinalAccessor),
            anyOnto(MARK, FinalAccessor),
            "a taint mark is not covered: prepend, never collapse"
        )

        // The identity does not hold across a mark, so an [any] behind one must not be absorbed.
        // (On the fact side an [any] below a mark is unconstructible outright; here it is enough
        // that the scan does not cross one.)
        assertEquals(
            listOf(AnyAccessor, MARK, AnyAccessor, FinalAccessor),
            anyOnto(MARK, AnyAccessor, FinalAccessor),
            "the inner [any] sits behind an uncovered accessor and stays where it is"
        )

        assertEquals(
            listOf(AnyAccessor, TYPE, AnyAccessor, FinalAccessor),
            anyOnto(TYPE, AnyAccessor, FinalAccessor),
            "a type-info accessor is not covered either"
        )

        assertEquals(
            listOf(AnyAccessor, FIELD_X, TYPE, AnyAccessor, FinalAccessor),
            anyOnto(FIELD_X, TYPE, AnyAccessor, FinalAccessor),
            "the covered prefix is walked, the uncovered accessor stops the scan"
        )
    }

    /* ---------- 3A: prependAccessor is symmetric again ---------- */

    @Test
    fun `prependAccessor keeps any on both an empty and a non-empty chain`() {
        val onEmpty = manager.mostAbstractInitialAp(base).prependAccessor(AnyAccessor)
        assertEquals(listOf(AnyAccessor), onEmpty.accessors(), "the empty-chain branch always kept it")

        val onNonEmpty = manager.createFinalInitialAp(base, ExclusionSet.Empty).prependAccessor(AnyAccessor)
        assertEquals(
            listOf(AnyAccessor, FinalAccessor),
            onNonEmpty.accessors(),
            "the addParent branch must agree with it"
        )
    }

    /* ---------- 3C: concat is fixed transitively by addParent ---------- */

    @Test
    fun `concat preserves an any in the left operand`() {
        val left = premise(AnyAccessor, FIELD_Y)
        val delta = AccessPath.AccessPathDelta.Delta(chain(FIELD_Z, FinalAccessor))

        assertEquals(
            listOf(AnyAccessor, FIELD_Y, FIELD_Z, FinalAccessor),
            left.concat(delta).accessors(),
            "concat re-prepends the left operand through addParent, so [any] now survives it"
        )
    }

    /* ---------- 3B: the repeated-field collapse must not cross an `[any]` ---------- */

    @Test
    fun `limitFieldAccess collapses a repeated field when no any separates the two`() {
        assertEquals(
            listOf(FIELD_Y, FIELD_B, FinalAccessor),
            chain(FIELD_X, FIELD_Y, FIELD_B, FinalAccessor).addParent(idx(FIELD_Y)).accessors(),
            "the cycle collapse itself is unchanged: y onto x.y.b.\$ is y.b.\$"
        )
    }

    @Test
    fun `limitFieldAccess does not collapse across an any`() {
        assertEquals(
            listOf(FIELD_Y, FIELD_X, AnyAccessor, FIELD_Y, FIELD_B, FinalAccessor),
            chain(FIELD_X, AnyAccessor, FIELD_Y, FIELD_B, FinalAccessor).addParent(idx(FIELD_Y)).accessors(),
            "an [any] between the two y's means they need not be the same y -- nothing is truncated"
        )
    }

    @Test
    fun `an any breaks an element run instead of being walked through`() {
        // [elem] and [any] are different accessors, and both limitElementAccess and
        // collapseElementAccess terminate at the first non-element accessor, so the run below the
        // [any] is left alone rather than fused with the one above it.
        assertEquals(
            listOf(ElementAccessor, ElementAccessor, AnyAccessor, ElementAccessor, FinalAccessor),
            chain(ElementAccessor, AnyAccessor, ElementAccessor, FinalAccessor)
                .addParent(idx(ElementAccessor)).accessors(),
            "the [any] terminates the element run above it"
        )
    }

    /* ---------- 3D: `[any]` is charged as a cost, `size` stays a link count ---------- */

    @Test
    fun `depth charges any at ten while size still counts it as one link`() {
        val withAny = premise(FIELD_X, AnyAccessor, FIELD_Y, FinalAccessor)

        assertEquals(4, withAny.size, "size is the literal link count -- filterStartsWith compares against it")
        assertEquals(1 + 10 + 1 + 1, withAny.depth, "[any] is charged the same 10 the fact side charges")

        val withoutAny = premise(FIELD_X, FIELD_Z, FIELD_Y, FinalAccessor)
        assertEquals(4, withoutAny.size)
        assertEquals(4, withoutAny.depth, "an [any]-free chain charges one per link")

        assertEquals(0, manager.mostAbstractInitialAp(base).depth, "the bare abstraction is still depth 0")
    }

    /* ---------- round trip ---------- */

    @Test
    fun `createNodeFromAccessors round-trips a chain containing an any`() {
        val accessors = IntArrayList()
        listOf(FIELD_X, AnyAccessor, MARK, FinalAccessor).forEach { accessors.add(idx(it)) }

        val node = assertNotNull(manager.createNodeFromAccessors(accessors))

        assertEquals(accessors, node.toList(), "raw construction must not rewrite the chain")
        assertEquals(listOf(FIELD_X, AnyAccessor, MARK, FinalAccessor), node.accessors())
    }

    /* ---------- 3H: getAllAccessors reports `[any]`, unlike the fact side ---------- */

    @Test
    fun `getAllAccessors reports the any accessor`() {
        assertEquals(
            setOf(AnyAccessor),
            premise(AnyAccessor).getAllAccessors(),
            "an [any]-only premise is not empty, but it is un-refined -- consumers must filter, not rely on isEmpty"
        )
    }
}
