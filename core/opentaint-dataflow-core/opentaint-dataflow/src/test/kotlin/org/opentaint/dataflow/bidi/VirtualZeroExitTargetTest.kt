package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Dp ZERO accepts both ZERO and Target, including a pair supplied by lazy AP completion. */
class VirtualZeroExitTargetTest {
    @Test fun `a virtual paired ZERO exit admits the same origin for AP ZERO and Target`() {
        val f = EngineShellFixtures()
        val ap = f.manager
        val t = MarkSlot.Concrete(ap.marks.mark("T"))
        val u = MarkSlot.Concrete(ap.marks.mark("U"))
        val path = listOf(ap.accessors.index(ClassStaticAccessor("C")), f.field("f"))
        fun static(mark: MarkSlot) = Pattern(PathFact(STATIC, path, Tail.STAR, mark), ExclusionSet.Empty)
        fun returned(mark: MarkSlot, tail: Tail = Tail.EXACT) =
            Pattern(PathFact(AccessPathBase.Return, emptyList(), tail, mark), ExclusionSet.Empty)
        val completed = FrozenStaticCompletion.Builder(ap, DetachedStaticCallGraph.EMPTY).apply {
            addBoundary(f.a, ap.zero.toPattern(), static(t))
            addBoundary(f.a, static(MarkSlot.STAR), returned(MarkSlot.STAR, Tail.STAR))
        }.build()
        val demand = DemandStore.Builder(ap).apply { withCompletion(completed) }.build()
        val policy = RestrictedInitialPolicy(2, 1, Direction.BACKWARD, ap.marks)
        val matching = ap.initial(returned(t))
        val other = ap.initial(returned(u))

        assertEquals(listOf(Reach.NORMAL), demand.intersect(f.a, matching, Reach.NORMAL, policy),
            "ZERO -> C.f/T plus C.f/FLOW -> ret/FLOW gives the virtual pair (ret/T, ZERO)")
        assertTrue(demand.acceptsTarget(f.a, matching, policy),
            "The same complete pair must admit Target because Dp ZERO accepts ZERO and Target")
        assertTrue(demand.intersect(f.a, other, Reach.NORMAL, policy).isEmpty())
        assertFalse(demand.acceptsTarget(f.a, other, policy), "A different mark has no paired ZERO exit")
        assertFalse(demand.acceptsTarget(f.a, ap.zero, policy), "The pair has a data entry, not a ZERO entry")
        assertTrue(demand.initials(f.a, Reach.NORMAL, policy).isEmpty(),
            "An ordinary data-to-ZERO virtual pair does not create a Target entry")
    }
}
