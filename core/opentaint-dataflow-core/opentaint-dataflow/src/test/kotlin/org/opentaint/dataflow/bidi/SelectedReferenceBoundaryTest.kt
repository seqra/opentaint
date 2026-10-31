package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.*
import org.opentaint.dataflow.bidi.interp.ZERO_FACT
import org.opentaint.dataflow.bidi.interp.ZERO_PATTERN
import kotlin.test.*

/** Keep the selected control table separate from the frozen local-report iteration controls. */
class SelectedReferenceBoundaryTest {
    @Test
    fun `selected exact admission rejects MAY while the labelled old table remains frozen`(): Unit =
        FiniteProgramFixtures().use { f ->
            val t = MarkSlot.Concrete(f.mark("T"))
            val exact = f.pattern(AccessPathBase.Argument(0), mark = t)
            val may = exact.copy(fact = exact.fact.copy(tail = Tail.ANY))
            val selected = SelectedDemandReference(3, 2, Direction.FORWARD, f.manager.marks, f.field("witness"))
            val old = SelectedDemandReference(3, 2, Direction.FORWARD, f.manager.marks, f.field("witness"),
                rejectMayForExact = false)
            assertNull(selected.emit(exact, may))
            assertEquals(exact, selected.emit(may, exact), "EXACT can still refine a MAY demand")
            assertEquals(exact, old.emit(exact, may), "The old table stays labelled, not applied to production")
        }

    @Test
    fun `selected restricted root needs ZERO guidance while preTargets keeps implicit entry`(): Unit =
        FiniteProgramFixtures().use { f ->
            val key = f.method("root", listOf(emptyList()), 0).key()
            val config = f.config(index = 3, roots = listOf(key))
            val selected = NaiveClosure(f, config, semantics = NaiveClosure.Semantics.SELECTED).run()
            val old = NaiveClosure(f, config, semantics = NaiveClosure.Semantics.PRE_TARGETS).run()
            assertTrue(selected.initials.isEmpty())
            assertContains(old.initials, ObservedInitial(key, ZERO_PATTERN))
        }

    @Test
    fun `selected backward ZERO summary uses paired C5 while preTargets keeps its old exception`(): Unit =
        FiniteProgramFixtures().use { f ->
            val key = f.method("root", listOf(emptyList()), 0).key()
            val t = MarkSlot.Concrete(f.mark("T"))
            val config = f.config(index = 2, roots = listOf(key), demand = listOf(key to DemandPattern(
                ZERO_PATTERN, f.pattern(AccessPathBase.Argument(0), mark = t))))
            val selected = NaiveClosure(f, config, semantics = NaiveClosure.Semantics.SELECTED).run()
            val old = NaiveClosure(f, config, semantics = NaiveClosure.Semantics.PRE_TARGETS).run()
            val zero = ObservedEdge(key, setOf(ZERO_PATTERN), Conclusion(ZERO_FACT, ExclusionSet.Empty, false))
            assertContains(selected.rawSummaries, zero)
            assertFalse(zero in selected.publications, "ZERO does not match the paired AP exit demand")
            assertContains(old.publications, zero, "Only the explicitly old reference has this exception")
        }
}
