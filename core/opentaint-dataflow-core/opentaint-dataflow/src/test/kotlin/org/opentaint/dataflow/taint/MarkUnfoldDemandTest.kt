package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import kotlin.test.Test
import kotlin.test.assertEquals

/**
 * What the demand remembers, and what it refuses.
 *
 * The key is the asking frame, the whole fact and the mark, so two different facts never share
 * a question and no answer can starve another depending on which arrives first. What stops the
 * self-similar loop is not the key but the fact's own path: an accessor already on it is never
 * demanded. Both halves are pinned here.
 */
class MarkUnfoldDemandTest {

    private val frameA = MethodEntryPoint(EmptyMethodContext, FakeInst("a"))
    private val frameB = MethodEntryPoint(EmptyMethodContext, FakeInst("b"))

    private val mark = TaintMarkAccessor("tainted")
    private val otherMark = TaintMarkAccessor("other")

    private val x: Accessor = FieldAccessor("C", "x", "C")
    private val y: Accessor = FieldAccessor("C", "y", "C")
    private val w: Accessor = FieldAccessor("C", "w", "C")

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())

    /** `base.accessors.*` */
    private fun fact(base: AccessPathBase, vararg accessors: Accessor): InitialFactAp =
        accessors.foldRight(manager.mostAbstractInitialAp(base)) { accessor, fact -> fact.prependAccessor(accessor) }

    private val arg0 = AccessPathBase.Argument(0)
    private val arg1 = AccessPathBase.Argument(1)

    @Test
    fun `an accessor is fresh once for a question`() {
        val demand = MarkUnfoldDemand()

        assertEquals(listOf(y), demand.demand(frameA, fact(arg0, x), mark, listOf(y)))
        assertEquals(emptyList(), demand.demand(frameA, fact(arg0, x), mark, listOf(y)))
    }

    @Test
    fun `only the part that is new comes back`() {
        val demand = MarkUnfoldDemand()

        demand.demand(frameA, fact(arg0), mark, listOf(x))
        assertEquals(listOf(y), demand.demand(frameA, fact(arg0), mark, listOf(x, y)))
    }

    @Test
    fun `the frame, the base and the mark each separate questions`() {
        val demand = MarkUnfoldDemand()
        demand.demand(frameA, fact(arg0), mark, listOf(x))

        assertEquals(listOf(x), demand.demand(frameB, fact(arg0), mark, listOf(x)))
        assertEquals(listOf(x), demand.demand(frameA, fact(arg1), mark, listOf(x)))
        assertEquals(listOf(x), demand.demand(frameA, fact(arg0), otherMark, listOf(x)))
    }

    /**
     * `arg0.x.*` and `arg0.w.*` are siblings, and `arg0.x.w.*` refines one of them: each is its
     * own abstraction and needs its own split. Sharing a question, only the one answered first
     * would get it.
     */
    @Test
    fun `different facts are separate questions`() {
        val demand = MarkUnfoldDemand()

        assertEquals(listOf(y), demand.demand(frameA, fact(arg0, x), mark, listOf(y)))
        assertEquals(listOf(y), demand.demand(frameA, fact(arg0, w), mark, listOf(y)))
        assertEquals(listOf(y), demand.demand(frameA, fact(arg0, x, w), mark, listOf(y)))
        assertEquals(listOf(y), demand.demand(frameA, fact(arg0), mark, listOf(y)))
    }

    /** An answer replaces the exclusions, so they are not part of what is asked. */
    @Test
    fun `exclusions do not separate questions`() {
        val demand = MarkUnfoldDemand()
        demand.demand(frameA, fact(arg0, x), mark, listOf(y))

        val excluded = fact(arg0, x).replaceExclusions(ExclusionSet.Empty.add(w))
        assertEquals(emptyList(), demand.demand(frameA, excluded, mark, listOf(y)))
    }

    /**
     * The loop: splitting `arg0.y.*` on `y` gives `arg0.y.y.*`, which asks again one accessor
     * further down. It is refused by the fact alone, whatever was demanded before.
     */
    @Test
    fun `an accessor already on the fact's path is never demanded`() {
        val demand = MarkUnfoldDemand()

        assertEquals(emptyList(), demand.demand(frameA, fact(arg0, y), mark, listOf(y)))
        assertEquals(emptyList(), demand.demand(frameA, fact(arg0, x, y), mark, listOf(y)))
        assertEquals(listOf(x), demand.demand(frameA, fact(arg0, y), mark, listOf(x, y)))
    }

    @Test
    fun `nothing demanded is nothing fresh`() {
        val demand = MarkUnfoldDemand()

        assertEquals(emptyList(), demand.demand(frameA, fact(arg0), mark, emptyList()))
    }

    /** The demand only ever uses an entry point as a map key, so identity is all it needs. */
    private class FakeInst(private val id: String) : CommonInst {
        override val location: CommonInstLocation get() = error("not used as a location")
        override fun toString(): String = id
    }
}
