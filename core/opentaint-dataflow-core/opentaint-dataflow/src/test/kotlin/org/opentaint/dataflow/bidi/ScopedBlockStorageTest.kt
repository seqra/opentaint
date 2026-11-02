package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** Control scopes are independent from the AP keys they store. */
class ScopedBlockStorageTest {
    private val fixture = StoreFixtures()
    private val ap = fixture.manager
    private val ops = fixture.ops
    private val method = fixture.method
    private val block = BlockId(2)
    private val entry = BlockScope(block, PortId(1))
    private val anotherEntry = BlockScope(block, PortId(2))
    private val exit = PortId(3)
    private val anotherExit = PortId(4)
    private val p = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val t = MarkSlot.Concrete(fixture.mark("T"))
    private val u = MarkSlot.Concrete(fixture.mark("U"))
    private fun pattern(base: AccessPathBase = p, path: List<Int> = emptyList(),
                        tail: Tail = Tail.ANY, mark: MarkSlot = t): Pattern =
        Pattern(PathFact(base, path, tail, mark), ExclusionSet.Empty)
    private fun facts(pattern: Pattern, layer: Layer = Layer.NORMAL) =
        ap.factsOf(pattern.fact, pattern.exclusion, layer)
    private val policy = RestrictedInitialPolicy(4, 5, Direction.BACKWARD, ap.marks)
    private fun decoded(values: List<Facts>) = values.flatMap { value ->
        ops.leaves(value).map { Conclusion(it.fact, it.exclusion, value.layer == Layer.DEMAND) }.toList()
    }.toSet()

    @Test fun `dense local point cells keep identical post statement facts independent`() {
        val points = object : PointDirectory<Int> {
            override val size = 2
            override fun index(point: Int) = when (point) { 70 -> 0; 1000 -> 1; else -> -1 }
        }
        val left = ScopedEdgeStore(ap, points, 3)
        val right = ScopedEdgeStore(ap, points, 3)
        val premise = ap.initial(pattern(tail = Tail.EXACT))
        val value = facts(pattern(ret, listOf(f), Tail.EXACT))
        assertNotNull(left.add(70, premise, value))
        assertNull(left.add(70, premise, value))
        assertTrue(left.edgesAt(1000).none())
        assertTrue(right.edgesAt(70).none())
        assertNotNull(right.add(70, premise, value))
        assertNotNull(left.add(1000, premise, value))
        assertFailsWith<IllegalArgumentException> { left.add(71, premise, value) }
    }

    @Test fun `entry admission unions its exits but cannot borrow another entry or public row`() {
        val builder = DemandStore.Builder(ap).apply {
            add(method, entry, exit, DemandPattern(pattern(), pattern(ret)))
            add(method, entry, anotherExit, DemandPattern(pattern(mark = u), pattern(ret, mark = u)))
            add(method, anotherEntry, exit, DemandPattern(pattern(path = listOf(g)), pattern(ret)))
            add(method, DemandPattern(pattern(path = listOf(f)), pattern(ret)))
        }
        val store = builder.build()
        val view = store.scope(method, entry)
        for (mark in listOf(t, u)) assertTrue(view.initials(facts(pattern(tail = Tail.EXACT, mark = mark)), policy).isNotEmpty())
        assertTrue(store.initials(method, facts(pattern(tail = Tail.EXACT)), policy).isEmpty())
        assertTrue(store.scope(method, anotherEntry).initials(facts(pattern(tail = Tail.EXACT)), policy).isEmpty())
        assertTrue(store.scope(method, BlockScope(BlockId(5), PortId(1)))
            .initials(facts(pattern(tail = Tail.EXACT)), policy).isEmpty())
        // A later builder mutation cannot mutate an existing scope snapshot.
        val late = BlockScope(BlockId(8), PortId(1))
        builder.add(method, late, exit, DemandPattern(pattern(), pattern(ret)))
        val actual = facts(pattern(tail = Tail.EXACT))
        assertTrue(store.scope(method, late).initials(actual, policy).isEmpty())
        assertTrue(builder.build().scope(method, late).initials(actual, policy).isNotEmpty())
    }

    @Test fun `paired intersection uses the actual exit and keeps its own budget`() {
        val shallow = pattern(ret)
        val deep = pattern(ret, listOf(f))
        val store = DemandStore.Builder(ap).apply {
            add(method, entry, exit, DemandPattern(pattern(), shallow))
            add(method, entry, anotherExit, DemandPattern(pattern(), deep))
        }.build()
        val initial = ap.initial(pattern(tail = Tail.EXACT))
        val raw = facts(pattern(ret, listOf(f, g), Tail.EXACT))
        val view = store.scope(method, entry)
        assertEquals(setOf(Conclusion(pattern(ret, listOf(f)).fact, ExclusionSet.Empty, true)),
            decoded(view.intersect(exit, initial, raw, policy)))
        assertEquals(setOf(Conclusion(pattern(ret, listOf(f, g), Tail.EXACT).fact, ExclusionSet.Empty, false)),
            decoded(view.intersect(anotherExit, initial, raw, policy)))
        assertTrue(view.intersect(PortId(9), initial, raw, policy).isEmpty())
        assertTrue(store.intersect(method, initial, raw, policy).isEmpty())
    }

    @Test fun `control rows never combine entry and exit permissions across scopes`() {
        val store = DemandStore.Builder(ap).apply {
            add(method, entry, exit, PairedDemand(DemandEntry.Target, DemandExit.Zero))
            add(method, entry, anotherExit, PairedDemand(DemandEntry.Data(pattern()), DemandExit.Zero))
            add(method, anotherEntry, exit, PairedDemand(DemandEntry.Zero, DemandExit.Data(pattern(ret))))
        }.build()
        val initial = ap.initial(pattern(tail = Tail.EXACT))
        val view = store.scope(method, entry)
        assertTrue(view.initials(Reach.NORMAL, policy).isNotEmpty())
        assertTrue(view.acceptsTarget(exit, ap.zero, policy))
        assertFalse(view.acceptsTarget(anotherExit, ap.zero, policy))
        assertTrue(view.acceptsTarget(anotherExit, initial, policy))
        assertFalse(view.acceptsTarget(exit, initial, policy))
        assertFalse(store.scope(method, anotherEntry).acceptsTarget(exit, ap.zero, policy))
    }

    @Test fun `saved native rows keep both ports and reverse their control roles`() {
        val initial = ap.initial(pattern(tail = Tail.EXACT))
        val value = facts(pattern(ret, listOf(f), Tail.EXACT))
        val store = PersistentRecordStore(ap)
        val row = Record(method, Direction.FORWARD, initial, value, entry, exit)
        store.add(row)
        assertEquals(listOf(row), store.byEntry(method, entry, initial.toPattern()).toList())
        assertTrue(store.byEntry(method, anotherEntry, initial.toPattern()).none())
        assertTrue(store.byEntry(method, initial.toPattern()).none())
        val reverseScope = BlockScope(block, exit)
        assertEquals(listOf(row), store.byExit(method, reverseScope, pattern(ret, listOf(f), Tail.EXACT)).toList())
        assertTrue(store.byExit(method, entry, pattern(ret, listOf(f), Tail.EXACT)).none())
        assertEquals(entry, row.scopeIn(Direction.FORWARD))
        assertEquals(exit, row.exitIn(Direction.FORWARD))
        assertEquals(reverseScope, row.scopeIn(Direction.BACKWARD))
        assertEquals(entry.entry, row.exitIn(Direction.BACKWARD))
        assertEquals(ScopedSummaryKey(method, reverseScope, entry.entry),
            ScopedSummaryKey(method, entry, exit).reversed())
        assertEquals(1, row.reversedAt(pattern(ret, listOf(f), Tail.EXACT)).count())
    }

    @Test fun `scoped persistence merges only the same complete port row and read view is immutable`() {
        val initial = ap.initial(pattern(tail = Tail.EXACT))
        fun summary(path: List<Int>) = RunSummaryStore(ap).apply {
            addAdmitted(initial, facts(pattern(ret, path, Tail.EXACT)))
            addAdmitted(initial, facts(pattern(ret, path), Layer.DEMAND))
        }
        val records = PersistentRecordStore(ap)
        records.persistScoped(Direction.FORWARD, sequenceOf(
            ScopedRunSummary(ScopedSummaryKey(method, entry, exit), summary(listOf(f))),
            ScopedRunSummary(ScopedSummaryKey(method, entry, anotherExit), summary(listOf(f))),
            ScopedRunSummary(ScopedSummaryKey(method, anotherEntry, exit), summary(listOf(g))),
        ))
        val rows = records.byEntry(method, entry, initial.toPattern()).toList()
        assertEquals(setOf(exit, anotherExit), rows.map { it.exit }.toSet())
        assertTrue(rows.all { it.conclusion.layer == Layer.NORMAL })
        assertEquals(1, records.byEntry(method, anotherEntry, initial.toPattern()).count())
        val readonly = records.view()
        assertFails { readonly.persistScoped(Direction.FORWARD, emptySequence()) }
        assertFails { readonly.add(rows.first()) }
    }

    @Test fun `saved normal targets retain local scope without becoming public zero reports`() {
        val initial = ap.initial(pattern(tail = Tail.EXACT))
        val id = ReportId(17)
        val root = OwnedNormalTarget(method, initial, ReportId(16))
        val local = OwnedNormalTarget(method, initial, id, entry)
        val localZero = OwnedNormalTarget(method, ap.zero, ReportId(18), entry)
        val targets = NormalTargetStore(ap, sequenceOf(root, local, localZero))
        assertTrue(targets.contains(method, initial, root.id))
        assertFalse(targets.contains(method, initial, id))
        assertTrue(targets.contains(method, entry, initial, id))
        assertFalse(targets.contains(method, anotherEntry, initial, id))
        val actual = facts(pattern(tail = Tail.EXACT))
        val mode = ApMode(false, Direction.FORWARD, 5)
        assertEquals(listOf(TargetSummary(initial, Target.NormalTarget(id)) to 0),
            targets.candidates(method, entry, initial, actual, mode))
        assertTrue(targets.candidates(method, anotherEntry, initial, actual, mode).isEmpty())
        assertEquals(setOf(root, local, localZero), targets.rows().toSet())
        assertTrue(targets.zeroRows().none())
    }

}
