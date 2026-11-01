package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Complete paired C5 selects first. Its own exit then sets the conclusion budget. */
class DemandRelativeRestrictionTest {
    private val fixture = StoreFixtures()
    private val ap = fixture.manager
    private val ops = fixture.ops
    private val arg = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val h = fixture.field("h")
    private val cls = ap.accessors.index(ClassStaticAccessor("Box"))
    private val element = ap.accessors.index(ElementAccessor)
    private val t = MarkSlot.Concrete(fixture.mark("T"))
    private fun p(base: AccessPathBase = ret, path: List<Int> = emptyList(), tail: Tail = Tail.ANY,
                  mark: MarkSlot = t, exclusion: ExclusionSet = ExclusionSet.Empty) =
        Pattern(PathFact(base, path, tail, mark), exclusion)
    private val entry get() = p(base = arg)
    private val initial get() = ap.initial(p(base = arg, tail = Tail.EXACT))
    private fun raw(pattern: Pattern, layer: Layer = Layer.NORMAL) =
        ap.factsOf(pattern.fact, pattern.exclusion, layer)
    private fun store(vararg exits: Pattern) = DemandStore.Builder(ap).apply {
        for (exit in exits) add(fixture.method, DemandPattern(entry, exit))
    }.build()
    private fun payload(values: List<Facts>) = values.flatMap { value -> ops.leaves(value).map {
        Conclusion(it.fact, it.exclusion, value.layer == Layer.DEMAND)
    }.toList() }.toSet()
    private fun policy(limit: Int) = RestrictedInitialPolicy(4, limit, Direction.BACKWARD, ap.marks)

    @Test fun `a depth zero exit cuts both normal and demand conclusions at one field`() {
        for (layer in Layer.entries) {
            val input = raw(p(path = listOf(f, g, h), tail = Tail.EXACT), layer)
            val output = store(p()).intersect(fixture.method, initial, input, policy(7))
            assertEquals(setOf(Conclusion(p(path = listOf(f)).fact, ExclusionSet.Empty, true)), payload(output))
        }
    }

    @Test fun `each complete row has its own budget and retains precise normal plus coarse demand in either order`() {
        val input = raw(p(path = listOf(f, g, h), tail = Tail.EXACT))
        val shallow = p()
        val deep = p(path = listOf(f, g))
        for (exits in listOf(arrayOf(shallow, deep), arrayOf(deep, shallow))) {
            val output = store(*exits).intersect(fixture.method, initial, input, policy(7))
            assertEquals(setOf(
                Conclusion(p(path = listOf(f)).fact, ExclusionSet.Empty, true),
                Conclusion(p(path = listOf(f, g, h), tail = Tail.EXACT).fact, ExclusionSet.Empty, false),
            ), payload(output))
        }
        val globallyCut = store(deep).intersect(fixture.method, initial, input, policy(2))
        assertEquals(setOf(Conclusion(p(path = listOf(f, g)).fact, ExclusionSet.Empty, true)), payload(globallyCut))
    }

    @Test fun `class anchors cost zero and element accessors consume one field`() {
        val static = raw(p(STATIC, listOf(cls, f, element, g), Tail.EXACT))
        val output = store(p(STATIC, listOf(cls, f))).intersect(fixture.method, initial, static, policy(7))
        assertEquals(setOf(Conclusion(p(STATIC, listOf(cls, f, element)).fact, ExclusionSet.Empty, true)), payload(output))
    }

    @Test fun `cut results retain concrete protection and flow mark exclusions but clear field exclusions`() {
        val input = (raw(p(path = listOf(f, g), tail = Tail.EXACT)) as TaintTree).let { it.withProtection(it.root) }
        val output = store(p()).intersect(fixture.method, initial, input, policy(7)).single() as TaintTree
        assertEquals(ops.leaves(output).toSet(), ops.leaves(checkNotNull(output.protectedPart())).toSet())
        val mark = MarkSlot.Star(ap.markSetOf(t.mark))
        val flowEntry = p(arg, tail = Tail.ANY, mark = MarkSlot.STAR)
        val flowInitial = ap.initial(p(arg, tail = Tail.STAR, mark = MarkSlot.STAR))
        val flow = raw(p(path = listOf(f, g), tail = Tail.STAR, mark = mark,
            exclusion = ExclusionSet.of(h)))
        val demand = DemandStore.Builder(ap).apply {
            add(fixture.method, DemandPattern(flowEntry, p(mark = MarkSlot.STAR)))
        }.build()
        val kept = demand.intersect(fixture.method, flowInitial, flow, policy(7))
        assertEquals(setOf(Conclusion(p(path = listOf(f), mark = mark).fact, ExclusionSet.Empty, true)), payload(kept))
        val within = p(path = listOf(f), tail = Tail.STAR, mark = mark, exclusion = ExclusionSet.of(h))
        assertEquals(setOf(Conclusion(within.fact, within.exclusion, false)),
            payload(demand.intersect(fixture.method, flowInitial, raw(within), policy(7))))
    }

    @Test fun `exact rejection happens before cutting and unrelated row permissions cannot cross`() {
        val input = raw(p(path = listOf(f, g), tail = Tail.EXACT))
        val demand = DemandStore.Builder(ap).apply {
            add(fixture.method, DemandPattern(entry, p(path = listOf(h), tail = Tail.EXACT)))
            add(fixture.method, DemandPattern(p(base = AccessPathBase.Argument(1)), p()))
        }.build()
        assertTrue(demand.intersect(fixture.method, initial, input, policy(7)).isEmpty())
    }

    @Test fun `ZERO control entries apply the same DATA cut while Reach retains its layer`() {
        val demand = DemandStore.Builder(ap).apply {
            add(fixture.method, PairedDemand(DemandEntry.Zero, DemandExit.Data(p())))
            add(fixture.method, PairedDemand(DemandEntry.Zero, DemandExit.Zero))
        }.build()
        val output = demand.intersect(fixture.method, ap.zero,
            raw(p(path = listOf(f, g), tail = Tail.EXACT)), policy(7))
        assertEquals(setOf(Conclusion(p(path = listOf(f)).fact, ExclusionSet.Empty, true)), payload(output))
        assertEquals(listOf(Reach.NORMAL), demand.intersect(fixture.method, ap.zero, Reach.NORMAL, policy(7)))
        assertEquals(listOf(Reach.DEMAND), demand.intersect(fixture.method, ap.zero, Reach.DEMAND, policy(7)))
        assertTrue(demand.acceptsTarget(fixture.method, ap.zero, policy(7)))
    }

    @Test fun `a precise local result cannot hide a shorter composed static row`() {
        val static = p(STATIC, listOf(cls, f), Tail.STAR)
        val completion = FrozenStaticCompletion.Builder(ap, DetachedStaticCallGraph.EMPTY).apply {
            addSeed(fixture.method, p(), static)
            addSeed(fixture.method, static, entry)
        }.build()
        val demand = DemandStore.Builder(ap).apply {
            add(fixture.method, DemandPattern(entry, p(path = listOf(f, g))))
            withCompletion(completion)
        }.build()
        val input = raw(p(path = listOf(f, g, h), tail = Tail.EXACT))
        assertEquals(setOf(
            Conclusion(p(path = listOf(f)).fact, ExclusionSet.Empty, true),
            Conclusion(p(path = listOf(f, g, h), tail = Tail.EXACT).fact, ExclusionSet.Empty, false),
        ), payload(demand.intersect(fixture.method, initial, input, policy(7))))
    }

    @Test fun `the cut uses the matched row and leaves the complete ND original unchanged`() {
        val other = ap.initial(p(AccessPathBase.Argument(1), listOf(f, g), Tail.EXACT))
        val original = ap.premiseOf(listOf(initial, other))
        val output = store(p()).intersect(fixture.method, original,
            raw(p(path = listOf(f, g, h), tail = Tail.EXACT)), policy(7))
        assertEquals(2, original.members.size)
        assertEquals(setOf(Conclusion(p(path = listOf(f)).fact, ExclusionSet.Empty, true)), payload(output))
    }

    @Test fun `shared static carry uses its own exit depth instead of the global budget`() {
        val demand = DemandStore.Builder(ap).apply { withSharedStaticCarry() }.build()
        val staticInitial = ap.initial(p(STATIC, listOf(cls, f), Tail.STAR))
        val input = raw(p(STATIC, listOf(cls, f, g, h), Tail.EXACT), Layer.DEMAND)
        assertEquals(setOf(Conclusion(p(STATIC, listOf(cls, f, g)).fact, ExclusionSet.Empty, true)),
            payload(demand.intersect(fixture.method, staticInitial, input,
                RestrictedInitialPolicy(2, 7, Direction.BACKWARD, ap.marks))))
    }

    @Test fun `packed complete row cuts equal a finite scalar per-row reference`() {
        val exits = listOf(p(), p(path = listOf(f)), p(path = listOf(f, g)))
        val inputLeaves = listOf(p(path = listOf(f, g, h), tail = Tail.EXACT),
            p(path = listOf(f, h), tail = Tail.EXACT), p(path = listOf(h), tail = Tail.EXACT))
        val input = inputLeaves.map { raw(it) }.reduce { a, b -> ap.mergeAddDelta(a, b).first }
        for (global in listOf(1, 2, 3, Int.MAX_VALUE)) {
            val q = policy(global)
            val expected = buildSet {
                for (exit in exits) for (leaf in inputLeaves) {
                    val selected = restrict(initial.toPattern(), Conclusion(leaf.fact, leaf.exclusion, false),
                        DemandPattern(entry, exit), ap.marks) ?: continue
                    val budget = minOf(global, exit.fact.path.count { it.isCounted() } + 1)
                    add(limit(selected, budget))
                }
            }
            assertEquals(expected, payload(store(*exits.toTypedArray()).intersect(fixture.method, initial, input, q)))
        }
    }

    @Test fun `optional counters count row and packet attempts without scalar fact enumeration`() {
        val property = "org.opentaint.bidi.optimizationStatistics"
        val previous = System.getProperty(property)
        val demand = try {
            System.setProperty(property, "true")
            store(p())
        } finally {
            if (previous == null) System.clearProperty(property) else System.setProperty(property, previous)
        }
        demand.intersect(fixture.method, initial, raw(p(path = listOf(f, g), tail = Tail.EXACT)), policy(7))
        val counters = checkNotNull(demand.staticCompletionStatistics())
        for (name in listOf("c5RowAttempts", "c5SelectedPackets", "c5LimitCalls", "c5LimitResults",
            "c5CutInputs", "c5NormalToDemandPackets", "c5LocalRows"))
            assertContains(counters, "$name=1")
        assertContains(counters, "c5ExactRejectRows=0")
        assertContains(counters, "c5MaxDepthRaw_2=1")
        assertContains(counters, "c5MaxDepthDp_0=1")
        assertContains(counters, "c5MaxDepthBudget_1=1")
        assertContains(counters, "c5MaxDepthSelected_2=1")
        assertContains(counters, "c5MaxDepthAdmitted_1=1")
    }
}
