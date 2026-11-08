package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.InitialDemandResults
import kotlin.test.*

/** Admission preserves uncertainty without changing caller input or the paired C5 permission. */
class InitialEmissionContractTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val ops = ApOps(ap)
    private val base = AccessPathBase.Argument(0)
    private val field = f.field("field")
    private val sibling = f.field("sibling")
    private val t = MarkSlot.Concrete(f.mark("T"))
    private val u = MarkSlot.Concrete(f.mark("U"))
    private fun p(path: List<Int> = emptyList(), tail: Tail = Tail.EXACT, mark: MarkSlot = t,
                  e: ExclusionSet = ExclusionSet.Empty, b: AccessPathBase = base) = Pattern(PathFact(b, path, tail, mark), e)
    private fun policy(run: Int = 2, limit: Int = 2) = RestrictedInitialPolicy(run, limit,
        if (run % 2 == 0) Direction.BACKWARD else Direction.FORWARD, ap.marks)

    @Test fun `concrete exact admission is directed and cannot turn MAY support into NORMAL`() {
        for (run in listOf(2, 3)) {
            val q = policy(run)
            val point = p(listOf(field))
            assertEquals(InitialEmission(point, Layer.NORMAL), q.emitAdmission(point, point, Layer.NORMAL))
            assertEquals(InitialEmission(point, Layer.DEMAND), q.emitAdmission(point, point, Layer.DEMAND))
            for (prefix in listOf(emptyList(), listOf(field))) {
                val may = p(prefix, Tail.ANY)
                assertEquals(InitialEmission(point, Layer.DEMAND), q.emitAdmission(point, may, Layer.DEMAND))
                assertEquals(InitialEmission(point, Layer.DEMAND), q.emitAdmission(point, may, Layer.NORMAL),
                    "Even a malformed NORMAL MAY label must not prove an exact point")
            }
            assertNull(q.emitAdmission(p(), p(listOf(field), Tail.ANY), Layer.DEMAND))
            assertNull(q.emitAdmission(point, p(listOf(sibling), Tail.ANY), Layer.DEMAND))
            assertNull(q.emitAdmission(point, p(tail = Tail.ANY, mark = u), Layer.DEMAND))
            assertNull(q.emitAdmission(point, p(tail = Tail.ANY, mark = MarkSlot.STAR), Layer.DEMAND))
            assertNull(q.emitAdmission(point, p(tail = Tail.ANY, b = AccessPathBase.Argument(1)), Layer.DEMAND))
            assertNull(policy(run, 1).emitAdmission(p(listOf(field, sibling)), p(tail = Tail.ANY), Layer.DEMAND))
        }
    }

    @Test fun `actual uniform exclusions still decide descent and invalid exact demand exclusions fail C2 and C5`() {
        val q = policy()
        val point = p(listOf(field))
        val must = p(tail = Tail.ANY_TAINT, e = ExclusionSet.of(sibling))
        assertEquals(InitialEmission(point, Layer.NORMAL), q.emitAdmission(point, must, Layer.NORMAL))
        assertEquals(InitialEmission(point, Layer.DEMAND), q.emitAdmission(point, must, Layer.DEMAND))
        assertNull(q.emitAdmission(point, must.copy(exclusion = ExclusionSet.of(field)), Layer.NORMAL))
        val invalid = point.copy(exclusion = ExclusionSet.of(sibling))
        assertNull(q.emit(invalid, point))
        assertNull(q.emitAdmission(invalid, point, Layer.NORMAL))
        assertFalse(q.canEmitInitial(invalid, point))
        assertFalse(q.canStoreInitial(invalid, point))
    }

    @Test fun `scalar actual views keep shared header E off exact and MAY leaves`() {
        val e = ExclusionSet.of(field)
        val leaf = ap.taintLeaves(ap.markSetOf(t.mark), ap.markSetOf(u.mark))
        val mixed = ap.taintTree(base, Layer.NORMAL, ap.taintAlg.leafNode(leaf), e, Tail.ANY_TAINT)
        assertEquals(setOf(p(), p(tail = Tail.ANY_TAINT, mark = u, e = e)), ops.leaves(mixed).toSet())
        val method = f.key("shared header exclusion")
        val blocked = p(listOf(field), mark = u)
        val admitted = p(listOf(sibling), mark = u)
        val demands = DemandStore.Builder(ap).apply {
            for (entry in listOf(p(), blocked, admitted))
                add(method, DemandPattern(entry, p(b = AccessPathBase.Return)))
        }.build()
        assertEquals(setOf(AdmittedInitial(ap.initial(p()), Layer.NORMAL),
            AdmittedInitial(ap.initial(admitted), Layer.NORMAL)), demands.initials(method, mixed, policy()))
        val may = ap.taintTree(base, Layer.DEMAND,
            ap.taintAlg.leafNode(ap.taintLeaves(MarkSet.EMPTY, ap.markSetOf(t.mark))), e, Tail.ANY)
        assertEquals(listOf(p(tail = Tail.ANY)), ops.leaves(may).toList(),
            "The typed factory removes illegal MAY E before C2 scalar views are read")
    }

    @Test fun `FLOW and ZERO keep their original admission policy while group guidance binds the actual full mark`() {
        val q = policy()
        val flow = p(mark = MarkSlot.STAR)
        assertNull(q.emitAdmission(flow, p(tail = Tail.ANY), Layer.DEMAND))
        assertNull(q.emitAdmission(flow.copy(fact = flow.fact.copy(path = listOf(field))), p(tail = Tail.ANY), Layer.DEMAND))
        assertEquals(InitialEmission(flow, Layer.NORMAL),
            q.emitAdmission(flow.copy(fact = flow.fact.copy(tail = Tail.ANY)), p(), Layer.DEMAND))
        val zero = ap.zero.toPattern()
        assertEquals(InitialEmission(zero, Layer.NORMAL), q.emitAdmission(zero, zero, Layer.DEMAND))
        assertNull(q.emitAdmission(zero, zero.copy(fact = zero.fact.copy(tail = Tail.ANY)), Layer.DEMAND))
        val group = MarkSlot.Concrete(ap.marks.group(ap.marks.groupOf(t.mark)))
        assertEquals(InitialEmission(p(), Layer.DEMAND),
            q.emitAdmission(p(mark = group), p(tail = Tail.ANY), Layer.DEMAND))
        assertNull(q.emitAdmission(p(mark = group), p(tail = Tail.ANY, mark = u), Layer.DEMAND))
    }

    @Test fun `query coverage keeps the concrete lane until both FLOW and concrete families are answered`() {
        val q = policy()
        val actual = p()
        val family = p(tail = Tail.ANY, mark = MarkSlot.STAR)
        val out = InitialDemandResults(ap, q, Layer.DEMAND)
        out.requireFamily(family, flow = true, actual = actual)
        assertFalse(out.fullyCovered)
        out.offer(family, actual)
        assertFalse(out.fullyCovered, "A legacy FLOW result must not hide the still-required concrete D lane")
        out.offer(family.copy(fact = family.fact.copy(mark = t)), actual)
        assertTrue(out.fullyCovered)
        assertEquals(setOf(AdmittedInitial(ap.initial(p(mark = MarkSlot.STAR)), Layer.NORMAL),
            AdmittedInitial(ap.initial(p()), Layer.DEMAND)), out.initials)
        val nonRefining = InitialDemandResults(ap, q, Layer.NORMAL)
        nonRefining.requireFamily(p(tail = Tail.ANY), flow = false, actual = p(tail = Tail.STAR))
        assertFalse(nonRefining.fullyCovered, "Same-head STAR now has a concrete primary and FLOW companion")
        nonRefining.offer(p(tail = Tail.ANY), p(tail = Tail.STAR))
        assertTrue(nonRefining.fullyCovered)
    }

    @Test fun `demand lookup emits both entry lanes over separate actual offers and C5 retains only its paired D output`() {
        val method = f.key("layered entry")
        val entry = p()
        val exit = p(mark = u, b = AccessPathBase.Return)
        val store = DemandStore.Builder(ap).apply { add(method, DemandPattern(entry, exit)) }.build()
        val q = policy()
        val weak = ap.factsOf(p(tail = Tail.ANY).fact, ExclusionSet.Empty, Layer.DEMAND)
        val exact = ap.factsOf(entry.fact, ExclusionSet.Empty, Layer.NORMAL)
        assertEquals(setOf(AdmittedInitial(ap.initial(entry), Layer.DEMAND)), store.initials(method, weak, q))
        assertEquals(setOf(AdmittedInitial(ap.initial(entry), Layer.NORMAL)), store.initials(method, exact, q),
            "The demand row is permission, not a permanent DEMAND start label")
        val raw = ap.factsOf(exit.fact, ExclusionSet.Empty, Layer.DEMAND)
        val kept = store.intersect(method, ap.initial(entry), raw, q)
        assertEquals(listOf(raw), kept)
        assertTrue(kept.all { it.layer == Layer.DEMAND })
        val unrelated = ap.factsOf(exit.fact.copy(base = AccessPathBase.Argument(1)), ExclusionSet.Empty, Layer.DEMAND)
        assertTrue(store.intersect(method, ap.initial(entry), unrelated, q).isEmpty())
        assertEquals(listOf(p(tail = Tail.ANY)), ops.leaves(weak).toList(),
            "Lookup does not change the submitted MAY fact")
    }
}
