package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Native late-iteration components from an explicit run-3 boundary, not a whole driver run.
 * The two F3 paired rows are explicit preconditions from the traced mapper.
 * All B4/F5 publications below are produced by its real method forms/C5.
 */
class ConductorUniformLateIterationsTest {
    private val fixture = MethodAnalysisFixtures(listOf(
        listOf(1), listOf(2, 3), listOf(5), listOf(4), listOf(5), listOf(6), emptyList()), 6)
    private val ap = fixture.manager
    private val ops = fixture.ops
    private val p = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return
    private val out = AccessPathBase.LocalVar(10)
    private val part = AccessPathBase.LocalVar(11)
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val h = fixture.field("h")
    private val extra = fixture.field("extra")
    private val e = ap.accessors.index(ElementAccessor)
    private val t = MarkSlot.Concrete(fixture.mark("T"))
    private val flow = MarkSlot.STAR
    private val policy4 = RestrictedInitialPolicy(4, 3, Direction.BACKWARD, ap.marks)

    init {
        fixture.statement(2, MicroEdgeBuilder().apply {
            write(out, listOf(e, h, extra), false, listOf(p), emptyList())
        }.build())
        fixture.statement(3, MicroEdgeBuilder().apply { read(part, p, listOf(f, g)) }.build())
        fixture.statement(4, MicroEdgeBuilder().apply {
            write(out, listOf(e, h), false, listOf(part), emptyList())
        }.build())
        fixture.statement(5, MicroEdgeBuilder().apply { move(ret, out) }.build())
    }

    @AfterTest fun closeFixture() = fixture.close()

    private fun pattern(base: AccessPathBase, path: List<Int>, tail: Tail = Tail.STAR,
                        mark: MarkSlot = flow) = fixture.pattern(base, path, tail, mark)
    private fun fact(base: AccessPathBase, path: List<Int>, tail: Tail, mark: MarkSlot = flow,
                     layer: Layer = Layer.NORMAL) = fixture.fact(base, path, tail, mark, layer = layer)

    private val demand4 get() = DemandStore.Builder(ap).apply {
        add(fixture.key, DemandPattern(pattern(ret, listOf(e, h), Tail.ANY), pattern(p, listOf(f))))
        add(fixture.key, DemandPattern(pattern(ret, listOf(e, h), Tail.ANY), pattern(p, emptyList())))
    }.build()

    private fun run4(): RunMethodAnalyzer {
        val actor = fixture.core(index = 4, L = 3, demand = demand4)
        val actual = fact(ret, listOf(e, h), Tail.EXACT, t)
        val starts = demand4.initials(fixture.key, actual, policy4)
        assertEquals(1, starts.size)
        assertEquals(pattern(ret, listOf(e, h), Tail.EXACT), starts.single().initial.toPattern())
        assertEquals(Layer.NORMAL, starts.single().layer)
        fixture.submitRestricted(actor, actual)
        fixture.drain(actor)
        return actor
    }

    private data class Row(val initial: Pattern, val output: Pattern, val layer: Layer)
    private fun rows(actor: RunMethodAnalyzer) = actor.summaries.all().flatMap { (initial, value) ->
        ops.leaves(value).map { Row((initial as InitialAp).toPattern(), it, value.layer) }
    }.toSet()

    private fun normalRead(actor: RunMethodAnalyzer): Record {
        val start = ap.initial(pattern(ret, listOf(e, h)))
        val expected = fact(p, listOf(f, g), Tail.STAR)
        assertTrue(Row(start.toPattern(), ops.leaves(expected).single(), Layer.NORMAL) in rows(actor))
        return Record(fixture.key, Direction.BACKWARD, start, expected)
    }

    @Test fun `run4 exact body generates both precise normal and shorter demand results`() {
        val actor = run4()
        val initial = pattern(ret, listOf(e, h))
        val expected = setOf(
            Row(initial, pattern(p, listOf(f, g)), Layer.NORMAL),
            Row(initial, pattern(p, listOf(f), Tail.ANY), Layer.DEMAND))
        val actual = rows(actor).filter { it.output.fact.base == p }.toSet()
        println("B4_ARG_ROWS $actual")
        assertEquals(expected, actual)
        assertFalse(actual.any { it.output.fact.path.isEmpty() }, "Do not start the live body from public STAR")
    }

    private class Output : LocalRelationOut {
        val values = ArrayList<Pair<PremiseKey, Facts>>()
        val targets = ArrayList<Pair<PremiseKey, Target>>()
        override fun data(original: PremiseKey, value: Facts) { values += original to value }
        override fun target(original: PremiseKey, target: Target) { targets += original to target }
        override fun markRequest(mark: TaintMark) = error("Concrete input needs no mark request")
    }

    @Test fun `run5 opposite normal replay transports uniform T and run4 reaches its real source`() {
        val normal = normalRead(run4())
        val actual = fact(p, listOf(f), Tail.ANY_TAINT, t)
        val result = Output()
        normal.forEachReversedAt(ops.leaves(actual).single()) { view, protected ->
            assertEquals(pattern(p, listOf(f, g)), view.premise)
            LocalRelationApplication(ops, ApMode(false, Direction.FORWARD, 4))
                .applyRecordView(actual, ap.zero, view, protected, result)
        }
        assertEquals(listOf<Pair<PremiseKey, Facts>>(ap.zero to fact(ret, listOf(e, h), Tail.ANY_TAINT, t)), result.values)
        assertIs<MarkCheck.Holds>(ops.checkMark(result.values.single().second,
            pattern(ret, listOf(e, h), Tail.EXACT, t), ApMode(false, Direction.FORWARD, 4)))

        val requirement = Output()
        LocalRelationApplication(ops, ApMode(false, Direction.BACKWARD, 3))
            .applyRecord(fact(ret, listOf(e, h), Tail.EXACT, t), ap.zero, normal, requirement)
        assertEquals(listOf<Pair<PremiseKey, Facts>>(ap.zero to fact(p, listOf(f, g), Tail.EXACT, t)), requirement.values)
        val source = Record(fixture.key, Direction.FORWARD, ap.zero, fact(p, listOf(f), Tail.ANY_TAINT, t))
        val discharge = Output()
        source.forEachReversedAt(ops.leaves(requirement.values.single().second).single()) { view, protected ->
            LocalRelationApplication(ops, ApMode(false, Direction.BACKWARD, 3))
                .applyRecordView(requirement.values.single().second, ap.zero, view, protected, discharge)
        }
        assertEquals(listOf<Pair<PremiseKey, Target>>(ap.zero to Target.DemandTarget), discharge.targets)
    }

    @Test fun `run5 child demand admits MUST and canonicalizes the covered deep copy before C5`() {
        val previous = run4()
        fixture.records.persist(Direction.BACKWARD, sequenceOf(fixture.key to previous.summaries))
        val demand5 = DemandStore.Builder(ap).apply {
            for ((initial, value) in previous.summaries.all()) if (value.layer == Layer.DEMAND)
                for (leaf in ops.leaves(value)) add(fixture.key, DemandPattern(leaf, (initial as InitialAp).toPattern()))
        }.build()
        val actual = fact(p, listOf(f), Tail.ANY_TAINT, t)
        val starts = demand5.initials(fixture.key, actual, RestrictedInitialPolicy(5, 4, Direction.FORWARD, ap.marks))
        assertEquals(setOf(AdmittedInitial(ap.initial(pattern(p, listOf(f), Tail.ANY_TAINT)), Layer.NORMAL)), starts.toSet())
        val actor = fixture.core(index = 5, L = 4, demand = demand5)
        fixture.submitRestricted(actor, actual)
        fixture.drain(actor)
        val initial = pattern(p, listOf(f), Tail.ANY_TAINT)
        val returned = rows(actor).filter { it.output.fact.base == ret }.toSet()
        println("F5_RETURN_ROWS $returned")
        val root = pattern(ret, listOf(e,h), Tail.ANY_TAINT)
        val descendant = pattern(ret, listOf(e,h,extra,f), Tail.ANY_TAINT)
        assertTrue(covers(root,descendant), "The selected MUST prefix covers the complete deep-copy region")
        val atReturn = actor.edges.edgesAt(fixture.inst(5),ap.initial(initial)).flatMap { (_,value) ->
            ops.leaves(value).map { Row(initial,it,value.layer) }
        }.filter { it.output.fact.base==ret }.toSet()
        assertEquals(setOf(Row(initial,root,Layer.NORMAL)),atReturn,
            "Canonical post-statement storage removes the deeper MUST before it becomes a C5 candidate")
        assertEquals(setOf(Row(initial,root,Layer.NORMAL)),returned)
        // Paired C5 still retains both budgets when both candidate rows exist. That
        // independent rule is checked in RedesignedInitialEmissionTest and the B4 case above.
    }
}
