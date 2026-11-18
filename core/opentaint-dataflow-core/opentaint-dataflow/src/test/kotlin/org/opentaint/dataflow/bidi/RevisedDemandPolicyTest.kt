package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.DemandEntry
import org.opentaint.dataflow.bidi.store.DemandExit
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.DetachedStaticCallGraph
import org.opentaint.dataflow.bidi.store.FrozenStaticCompletion
import org.opentaint.dataflow.bidi.store.PairedDemand
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class RevisedDemandPolicyTest {
    private val fixture = EngineShellFixtures()
    private val ap = fixture.manager
    private val ops = fixture.ops
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val h = fixture.field("h")
    private val arg = AccessPathBase.Argument(0)
    private val t = MarkSlot.Concrete(ap.marks.mark("T"))
    private val u = MarkSlot.Concrete(ap.marks.mark("U"))

    private fun p(tail: Tail, mark: MarkSlot = t, path: List<Int> = emptyList(),
                  e: ExclusionSet = ExclusionSet.Empty, base: AccessPathBase = arg) =
        Pattern(PathFact(base, path, tail, mark), e)

    private fun policy(run: Int = 3, limit: Int = 4) =
        RestrictedInitialPolicy(run, limit, catalog = ap.marks, revised = true)

    private fun facts(p: Pattern, layer: Layer) = ap.factsOf(p.fact, p.exclusion, layer)

    @Test fun `MAY splits and NE removes the exact root`() {
        val may = p(Tail.ANY)
        val ne = p(Tail.NON_EMPTY_MAY)
        val point = InitialEmission(p(Tail.EXACT), Layer.DEMAND)
        val suffix = InitialEmission(p(Tail.STAR), Layer.DEMAND)
        val companion = InitialEmission(p(Tail.STAR, MarkSlot.STAR), Layer.NORMAL)
        assertEquals(setOf(point, suffix, companion), policy().emitAdmissions(may, may, Layer.DEMAND).toSet())
        assertEquals(setOf(suffix, companion), policy().emitAdmissions(ne, may, Layer.DEMAND).toSet())
        assertTrue(policy().emitAdmissions(ne, p(Tail.EXACT), Layer.NORMAL).isEmpty())
        assertTrue(policy().emitAdmissions(may, p(Tail.EXACT, u), Layer.NORMAL).isEmpty())
    }

    @Test fun `actual mask moves only under the selected deeper MUST exception`() {
        val fields = listOf(f, g, h)
        val e = ExclusionSet.of(f)
        val actual = p(Tail.ANY_TAINT, path = fields, e = e)
        val expected = setOf(InitialEmission(p(Tail.STAR, path = fields, e = e), Layer.DEMAND),
            InitialEmission(p(Tail.STAR, MarkSlot.STAR, fields, e), Layer.NORMAL),
            InitialEmission(p(Tail.EXACT, MarkSlot.STAR), Layer.NORMAL))
        assertEquals(expected, policy().emitAdmissions(p(Tail.ANY), actual, Layer.NORMAL).toSet())
        assertEquals(expected - InitialEmission(p(Tail.EXACT, MarkSlot.STAR), Layer.NORMAL),
            policy().emitAdmissions(p(Tail.NON_EMPTY_MAY), actual, Layer.NORMAL).toSet())
        val ordinary = policy().emitAdmissions(p(Tail.ANY), actual.copy(exclusion = ExclusionSet.Empty), Layer.NORMAL)
        assertTrue(ordinary.all { it.pattern.fact.path.size <= 1 })
        assertFalse(policy(limit = 2).canStoreInitial(p(Tail.ANY), p(Tail.STAR, path = fields, e = e)))
    }

    @Test fun `a possible child is tied to the same complete paired row when published`() {
        val root = p(Tail.ANY)
        val want = p(Tail.STAR, base = AccessPathBase.Return)
        val child = p(Tail.NON_EMPTY_MAY, path = listOf(f))
        val unrelated = p(Tail.EXACT, base = AccessPathBase.Return)
        val store = DemandStore.Builder(ap).apply {
            add(fixture.a, DemandPattern(root, want))
            add(fixture.a, DemandPattern(child, unrelated))
        }.build()
        val rootPair = PairedDemand(DemandEntry.Data(root), DemandExit.Data(want))
        val offer = facts(p(Tail.STAR), Layer.DEMAND)
        val guarded = store.boundInitials(fixture.a, offer, policy()) {
            sequenceOf(p(Tail.STAR, MarkSlot.STAR, listOf(f, g)))
        }
        val exactChild = guarded.single { command ->
            command.qualification?.row == rootPair && command.admitted.initial.toPattern() == p(Tail.EXACT, path = listOf(f))
        }
        assertTrue(exactChild.possible)
        assertEquals(p(Tail.STAR), exactChild.actual)
        val output = facts(p(Tail.EXACT, base = AccessPathBase.Return), Layer.DEMAND)
        val published = store.intersectAdmitted(fixture.a, exactChild.admitted.initial, output, policy())
        assertTrue(published.any { it.qualification?.matches(exactChild.qualification) == true })
        assertFalse(published.any {
            it.qualification?.row == PairedDemand(DemandEntry.Data(child), DemandExit.Data(unrelated))
        })
    }

    @Test fun `C5 checks raw point membership before normalization and then cuts by its own exit`() {
        val flow = MarkSlot.STAR
        val root = p(Tail.NON_EMPTY_MAY, flow)
        val short = p(Tail.STAR, flow, base = AccessPathBase.Return)
        val deep = p(Tail.STAR, flow, listOf(f, g), base = AccessPathBase.Return)
        val demand = DemandStore.Builder(ap).apply {
            add(fixture.a, DemandPattern(root, short))
            add(fixture.a, DemandPattern(root, deep))
        }.build()
        val output = facts(p(Tail.STAR, flow, listOf(f, g, h), base = AccessPathBase.Return), Layer.NORMAL)
        assertTrue(demand.intersectAdmitted(fixture.a, ap.initial(p(Tail.EXACT, flow)), output, policy()).isEmpty())
        val star = ap.initial(p(Tail.STAR, flow))
        val published = demand.intersectAdmitted(fixture.a, star, output, policy())
        assertEquals(setOf(Layer.NORMAL, Layer.DEMAND), published.map { it.facts.layer }.toSet())
        val shortResult = published.single { it.facts.layer == Layer.DEMAND }
        assertEquals(Layer.DEMAND, shortResult.facts.layer)
        assertEquals(p(Tail.NON_EMPTY_MAY, flow, listOf(f), base = AccessPathBase.Return),
            ops.leaves(shortResult.facts).single())
        assertEquals(output, published.single { it.facts.layer == Layer.NORMAL }.facts)
    }

    @Test fun `possible Target delivery needs the entire DATA to ZERO pair at its actual exit`() {
        val child = p(Tail.ANY, path = listOf(f))
        val exit = PortId(2)
        val differentExit = PortId(3)
        val scope = BlockScope(BlockId(1), PortId(1))
        val row = PairedDemand(DemandEntry.Data(child), DemandExit.Zero)
        val store = DemandStore.Builder(ap).apply {
            add(fixture.a, scope, exit, row)
        }.build().scope(fixture.a, scope)
        val starts = store.boundInitials(facts(p(Tail.STAR), Layer.DEMAND), policy())
        val point = starts.single { it.admitted.initial.tail == Tail.EXACT }
        assertTrue(point.possible)
        assertTrue(store.acceptsTarget(exit, point.admitted.initial, policy()))
        assertFalse(store.acceptsTarget(differentExit, point.admitted.initial, policy()))
        val qualifications = store.targetQualifications(exit, point.admitted.initial, policy())
        assertTrue(qualifications.single().matches(point.qualification))
        assertTrue(store.targetQualifications(differentExit, point.admitted.initial, policy()).isEmpty())
    }

    @Test fun `one ND arm qualifies the original and a cut preserves literal protection`() {
        val selected = ap.initial(p(Tail.EXACT))
        val other = ap.initial(p(Tail.EXACT, u, base = AccessPathBase.Argument(1)))
        val premise = ap.premiseOf(listOf(selected, other))
        val want = p(Tail.STAR, base = AccessPathBase.Return)
        val store = DemandStore.Builder(ap).apply {
            add(fixture.a, DemandPattern(p(Tail.ANY), want))
        }.build()
        val raw = facts(p(Tail.EXACT, path = listOf(f, g), base = AccessPathBase.Return), Layer.NORMAL)
        val protected = ap.selectedProtection(raw, null)
        val plainResult = store.intersectAdmitted(fixture.a, premise, raw, policy()).single()
        val protectedResult = store.intersectAdmitted(fixture.a, premise, protected, policy()).single()
        assertEquals(premise, plainResult.premise)
        assertEquals(premise, protectedResult.premise)
        assertEquals(ops.leaves(plainResult.facts).toList(), ops.leaves(protectedResult.facts).toList())
        assertFalse((plainResult.facts as TaintTree).protectionClass())
        assertTrue((protectedResult.facts as TaintTree).protectionClass())
        assertEquals(Tail.NON_EMPTY_MAY, (protectedResult.facts as TaintTree).anyTail)
    }

    @Test fun `a virtual static entry qualifies only its own full C5 composition`() {
        val cls = ap.accessors.index(ClassStaticAccessor("C"))
        val stat = p(Tail.STAR, MarkSlot.STAR, listOf(cls, g), base = STATIC)
        val entry = p(Tail.ANY, MarkSlot.STAR, listOf(f))
        val frozen = FrozenStaticCompletion.Builder(ap, DetachedStaticCallGraph.EMPTY).apply {
            addSeed(fixture.a, stat, entry)
        }.build()
        val store = DemandStore.Builder(ap).apply { withCompletion(frozen) }.build()
        val policy = policy(run = 2, limit = 1)
        val actual = facts(p(Tail.STAR, MarkSlot.STAR), Layer.NORMAL)
        val bound = store.boundInitials(fixture.a, actual, policy).single { it.admitted.initial.tail == Tail.EXACT }
        assertTrue(bound.possible)
        assertEquals(DemandEntry.Data(entry), bound.qualification?.virtualEntry)
        val raw = facts(stat, Layer.NORMAL)
        val publication = store.intersectAdmitted(fixture.a, bound.admitted.initial, raw, policy).single()
        assertEquals(Tail.STAR, (publication.premise as InitialAp).tail)
        assertEquals(PairedDemand(DemandEntry.Data(entry), DemandExit.Data(stat)), publication.qualification?.row)
        assertTrue(publication.qualification?.matches(bound.qualification) == true)
    }

    @Test fun `an exact static read cannot compose with a same head NE writer`() {
        val cls = ap.accessors.index(ClassStaticAccessor("C"))
        val field = p(Tail.NON_EMPTY_MAY, path = listOf(cls, g), base = STATIC)
        val point = field.copy(fact = field.fact.copy(tail = Tail.EXACT))
        val input = p(Tail.STAR)
        val reader = p(Tail.ANY, base = AccessPathBase.Return)
        fun view(writer: Pattern): DemandStore {
            val frozen = FrozenStaticCompletion.Builder(ap, DetachedStaticCallGraph.EMPTY).apply {
                addSeed(fixture.a, input, writer)
                addSeed(fixture.a, point, reader)
            }.build()
            return DemandStore.Builder(ap).apply { withCompletion(frozen) }.build()
        }
        val policy = policy(run = 2, limit = 1)
        val output = facts(input, Layer.DEMAND)
        val start = ap.initial(reader.copy(fact = reader.fact.copy(tail = Tail.EXACT)))
        assertTrue(view(field).intersectAdmitted(fixture.a, start, output, policy).isEmpty())
        assertTrue(view(point).intersectAdmitted(fixture.a, start, output, policy).isNotEmpty())
    }

    @Test fun `the inverse finds the same raw commands as exhaustive bounded offers`() {
        val element = ap.accessors.index(ElementAccessor)
        val fields = listOf(f, g, element)
        val paths = listOf(emptyList<Int>()) + fields.map { listOf(it) } +
            fields.flatMap { a -> fields.map { b -> listOf(a, b) } }
        val masks = listOf(ExclusionSet.Empty, ExclusionSet.of(f), ExclusionSet.of(g))
        for (run in listOf(2, 3)) {
            val q = policy(run, limit = 2)
            val input = paths.flatMap { path ->
                Tail.entries.filter { run != 2 || it != Tail.ANY_TAINT }.flatMap { tail ->
                    listOf(t, MarkSlot.STAR).flatMap { mark ->
                        val allowed = if (tail in setOf(Tail.STAR, Tail.ANY_TAINT)) masks else masks.take(1)
                        val layer = if (tail.isMay || tail == Tail.STAR && mark == t) Layer.DEMAND else Layer.NORMAL
                        allowed.map { p(tail, mark, path, it) to layer }
                    }
                }
            }
            for (path in paths) for (tail in listOf(Tail.EXACT, Tail.STAR, Tail.ANY, Tail.NON_EMPTY_MAY))
                for (mark in listOf(t, MarkSlot.STAR)) {
                    val entry = p(tail, mark, path)
                    val image = input.flatMap { (offer, layer) -> q.emitAdmissions(entry, offer, layer).map { it.pattern } }.toSet()
                    for ((test, _) in input) assertEquals(test in image, q.canStoreInitial(entry, test),
                        "run=$run entry=$entry candidate=$test")
                }
        }
    }
}
