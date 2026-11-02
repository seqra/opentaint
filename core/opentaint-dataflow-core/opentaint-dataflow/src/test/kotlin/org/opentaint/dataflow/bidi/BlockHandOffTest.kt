package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.ScopedTargetRows
import org.opentaint.dataflow.bidi.driver.projectBlockHandOff
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.engine.TargetSummary
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class BlockHandOffTest {
    private val fixture = StoreFixtures()
    private val ap = fixture.manager
    private val method = fixture.method
    private val scope = BlockScope(BlockId(1), PortId(3))
    private val exit = PortId(7)
    private val key = ScopedSummaryKey(method, scope, exit)
    private val t = MarkSlot.Concrete(fixture.mark("T"))
    private fun p(base: AccessPathBase, tail: Tail = Tail.EXACT, mark: MarkSlot = t) =
        Pattern(PathFact(base, emptyList(), tail, mark), ExclusionSet.Empty)
    private fun raw(pattern: Pattern, layer: Layer) = ap.factsOf(pattern.fact, pattern.exclusion, layer)
    private val arg = p(AccessPathBase.Argument(0))
    private val ret = p(AccessPathBase.Return, Tail.ANY)
    private fun policy(direction: Direction) = RestrictedInitialPolicy(4, 5, direction, ap.marks)

    @Test fun `forward block demands reverse both control ports and whole paired AP rows`() {
        val initial = ap.initial(arg)
        val rows = RunSummaryStore(ap).apply {
            addAdmitted(initial, raw(ret, Layer.DEMAND))
            // A NORMAL singleton does not create a second continuation row.
            addAdmitted(initial, raw(p(AccessPathBase.Return), Layer.NORMAL))
        }
        val builder = DemandStore.Builder(ap)
        val counts = LinkedHashMap<MethodKey, Int>()
        val boundaries = ArrayList<Pair<Pattern, Pattern>>()
        projectBlockHandOff(ap, Direction.FORWARD, false,
            sequenceOf(ScopedRunSummary(key, rows)), emptySequence(), builder, counts) { producer, from, to ->
            assertEquals(key, producer)
            boundaries += Pair(from, to)
        }
        val demand = builder.build()
        val opposite = demand.scope(method, key.reversed().scope)
        assertEquals(mapOf(method to 1), counts)
        assertEquals(listOf(arg to ret), boundaries)
        val actual = raw(p(AccessPathBase.Return), Layer.NORMAL)
        val admitted = opposite.initials(actual, policy(Direction.BACKWARD)).single()
        val wanted = raw(arg, Layer.NORMAL)
        assertTrue(opposite.intersect(scope.entry, admitted.initial, wanted, policy(Direction.BACKWARD)).isNotEmpty())
        assertTrue(opposite.intersect(exit, admitted.initial, wanted, policy(Direction.BACKWARD)).isEmpty())
        assertTrue(demand.scope(method, scope).initials(actual, policy(Direction.BACKWARD)).isEmpty())
        assertTrue(demand.initials(method, actual, policy(Direction.BACKWARD)).isEmpty())
    }

    @Test fun `normal backward ZERO rows retain existing source continuation selection`() {
        val rows = RunSummaryStore(ap).apply { addAdmitted(ap.zero, raw(arg, Layer.NORMAL)) }
        val builder = DemandStore.Builder(ap)
        val counts = LinkedHashMap<MethodKey, Int>()
        projectBlockHandOff(ap, Direction.BACKWARD, false,
            sequenceOf(ScopedRunSummary(key, rows)), emptySequence(), builder, counts)
        val view = builder.build().scope(method, key.reversed().scope)
        val seed = view.initials(raw(arg, Layer.NORMAL), policy(Direction.FORWARD)).single()
        assertTrue(view.intersect(scope.entry, seed.initial, Reach.NORMAL, policy(Direction.FORWARD)).isNotEmpty())
        assertEquals(1, counts[method])
    }

    @Test fun `forward ND guidance views each arm but count ignores duplicate exact normalized rows`() {
        val i1 = ap.initial(arg)
        val i2 = ap.initial(p(AccessPathBase.Argument(1)))
        val nd = ap.premiseOf(listOf(i1, i2))
        val rows = RunSummaryStore(ap).apply { addAdmitted(nd, raw(p(AccessPathBase.Return), Layer.NORMAL)) }
        val builder = DemandStore.Builder(ap)
        val counts = LinkedHashMap<MethodKey, Int>()
        // The second offer is a duplicate, not another unit of guidance.
        projectBlockHandOff(ap, Direction.FORWARD, false,
            sequenceOf(ScopedRunSummary(key, rows), ScopedRunSummary(key, rows)), emptySequence(), builder, counts)
        val view = builder.build().scope(method, key.reversed().scope)
        val seed = view.initials(raw(p(AccessPathBase.Return), Layer.NORMAL), policy(Direction.BACKWARD)).single()
        assertTrue(view.intersect(scope.entry, seed.initial, raw(arg, Layer.NORMAL), policy(Direction.BACKWARD)).isNotEmpty())
        assertTrue(view.intersect(scope.entry, seed.initial, raw(i2.toPattern(), Layer.NORMAL), policy(Direction.BACKWARD)).isNotEmpty())
        assertEquals(2, counts[method])
        assertFails {
            projectBlockHandOff(ap, Direction.BACKWARD, false,
                sequenceOf(ScopedRunSummary(key, rows)), emptySequence(), DemandStore.Builder(ap), LinkedHashMap())
        }
    }

    @Test fun `typed terminal keeps logical exit separate from physical data ports`() {
        val builder = DemandStore.Builder(ap)
        val counts = LinkedHashMap<MethodKey, Int>()
        projectBlockHandOff(ap, Direction.FORWARD, false, emptySequence(),
            sequenceOf(ScopedTargetRows(method, scope, listOf(TargetSummary(ap.zero, Target.DemandTarget)))),
            builder, counts)
        val demand = builder.build()
        val terminal = demand.scope(method, BlockScope(scope.block, PortId.ROOT_EXIT))
        assertTrue(terminal.initials(Reach.NORMAL, policy(Direction.BACKWARD)).isNotEmpty())
        assertTrue(terminal.acceptsTarget(scope.entry, ap.zero, policy(Direction.BACKWARD)))
        assertFalse(terminal.acceptsTarget(exit, ap.zero, policy(Direction.BACKWARD)))
        assertTrue(demand.scope(method, BlockScope(scope.block, exit))
            .initials(Reach.NORMAL, policy(Direction.BACKWARD)).isEmpty())
        assertEquals(1, counts[method])
    }
}
