package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

class RuntimeDataDomainTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val literal = AccessPathBase.Constant("java.lang.String", "safe")
    private val argument = AccessPathBase.Argument(0)
    private val mark = MarkSlot.Concrete(fixture.mark("T"))
    private fun initial(base: AccessPathBase = argument, tail: Tail = Tail.EXACT,
                        mark: MarkSlot = this.mark): InitialAp =
        m.initial(base, null, tail, ExclusionSet.Empty, mark)

    @Test fun `runtime domain rejects both endpoints for every tail and layer without changing generic AP factories`() {
        for (tail in Tail.entries) for (layer in Layer.entries) for (slot in listOf(mark, MarkSlot.STAR)) {
            val origin = initial(tail = tail, mark = slot)
            val constantOrigin = initial(literal, tail, slot)
            val value = fixture.fact(tail = tail, mark = slot, layer = layer)
            val constantValue = fixture.fact(base = literal, tail = tail, mark = slot, layer = layer)
            assertTrue(RuntimeDataDomain.packet(origin, value))
            assertFalse(RuntimeDataDomain.packet(constantOrigin, value))
            assertFalse(RuntimeDataDomain.packet(origin, constantValue))
            assertEquals(literal, constantOrigin.base)
            assertEquals(literal, constantValue.base)
        }
        assertTrue(RuntimeDataDomain.packet(m.zero, Reach.NORMAL))
    }

    @Test fun `one constant ND member rejects the full membership before a join can complete`() {
        val concrete = initial()
        val invalid = m.premiseOf(listOf(concrete, initial(literal)))
        assertEquals(2, invalid.size)
        val value = fixture.fact()
        val store = ConjunctionStore(m)
        assertTrue(store.addBinding("rule", fixture.inst(1), 2, 0,
            ConjunctionStore.Input(invalid, Layer.NORMAL, value)).isEmpty())
        assertTrue(store.addBinding("rule", fixture.inst(1), 2, 1,
            ConjunctionStore.Input(concrete, Layer.NORMAL, value)).isEmpty())
        val completed = store.addBinding("rule", fixture.inst(1), 2, 0,
            ConjunctionStore.Input(concrete, Layer.NORMAL, value))
        assertEquals(1, completed.size)
        assertTrue(completed.single().inputs.all { it.premise === concrete })
    }

    @Test fun `executable stores reject constants before initial output or native record retention`() {
        val invalid = initial(literal)
        val normal = fixture.fact()
        val constant = fixture.fact(base = literal)
        val initials = InitialFactStore()
        assertFalse(initials.add(invalid))
        assertTrue(initials.all().isEmpty())
        val edges = MethodEdgeStore(m, fixture.method, fixture.lm, 1)
        val summaries = RunSummaryStore(m, flowBacked = true)
        for ((premise, value) in listOf(invalid to normal, initial() to constant,
            m.premiseOf(listOf(initial(), invalid)) to normal)) {
            assertNull(edges.add(fixture.inst(1), premise, value))
            assertNull(summaries.add(premise, value))
            assertNull(summaries.addDemand(premise, value))
        }
        assertTrue(edges.edgesAt(fixture.inst(1)).none())
        assertTrue(summaries.all().none())
        assertTrue(summaries.demandEdges().none())
        val records = PersistentRecordStore(m)
        records.add(Record(fixture.method, Direction.FORWARD, invalid, normal))
        records.add(Record(fixture.method, Direction.FORWARD, initial(), constant))
        assertTrue(records.byEntry(fixture.method, initial().toPattern()).none())
        assertTrue(records.byExit(fixture.method, fixture.pattern()).none())
    }

    @Test fun `static fields including final or enum fields remain ordinary runtime data`() {
        val cls = m.accessors.index(ClassStaticAccessor("EnumType"))
        val field = fixture.field("VALUE")
        val premise = m.initial(STATIC, m.path(listOf(cls, field)), Tail.EXACT,
            ExclusionSet.Empty, mark)
        val facts = fixture.fact(STATIC, listOf(cls, field), mark = mark)
        assertTrue(RuntimeDataDomain.packet(premise, facts))
        val store = RunSummaryStore(m)
        assertNotNull(store.add(premise, facts))
        assertEquals(1, store.all().count())
    }

    @Test fun `constant requests and call input storage have no delta`() {
        val ref = CallerRef(fixture.method, initial(), Layer.NORMAL, fixture.inst(1))
        val added = AddedFactAccumulator(m)
        assertNull(added.add(ref, Layer.NORMAL, fixture.fact(literal)))
        assertNull(added.add(ref.copy(premise = initial(literal)), Layer.NORMAL, fixture.fact()))
        assertEquals(0, added.size)
        assertNull(Run1Slot.fromInitial(initial(literal, Tail.STAR, MarkSlot.STAR)))
        val requests = RequestStorage()
        assertTrue(requests.addAll(Run1Slot.Base(literal), RequestMarkSet.of(mark.mark)).isEmpty)
        assertTrue(requests.isEmpty)
        assertTrue(requests.borrowMatchingRows(fixture.fact(literal), {}).isEmpty())
    }

    @Test fun `invalid packed packets are consumed without selecting scalar fallback`() {
        val shape = initial(tail = Tail.STAR, mark = MarkSlot.STAR)
        val geometry = FlowAlgebra.LEAF_NODE
        val marks = m.markSetOf(mark.mark)
        val invalid = DiagonalDelta(shape, literal, Layer.DEMAND, geometry, marks, protected = false)
        val store = MethodEdgeStore(m, fixture.method, fixture.lm, 1, flowBacked = true)
        assertEquals(emptyList(), store.addDiagonal(fixture.inst(1), invalid))
        assertNull(NeutralRelationBatch.fromDiagonal(m, invalid))
        assertNull(NeutralRelationBatch.toDiagonal(m, shape,
            fixture.fact(literal, tail = Tail.STAR, layer = Layer.DEMAND) as TaintTree, marks))
        NeutralRelationBatch.decodePacked(m, shape,
            fixture.fact(literal, tail = Tail.STAR, layer = Layer.DEMAND) as TaintTree, marks) { _, _ ->
            fail("Invalid packed data must not decode")
        }
        assertTrue(store.edgesAt(fixture.inst(1)).none())
    }

    @Test fun `constant transfer is skipped but the literal overwrite still kills the old field`() {
        MethodAnalysisFixtures().use { f ->
            val core = f.core(index = 3)
            val field = f.store.field("value")
            val sibling = f.store.field("other")
            val summary = MicroEdgeBuilder().apply {
                write(argument, listOf(field), weak = false, values = listOf(literal), aliasPaths = emptyList())
            }.build()
            val premise = f.manager.initial(argument, null, Tail.EXACT, ExclusionSet.Empty,
                MarkSlot.Concrete(f.mark("T")))
            val outputs = ArrayList<Facts>()
            fun apply(path: List<Int>) {
                core.applier.statement(summary, premise, f.fact(argument, path),
                    Place(f.inst(1), statementEdge = false, sources = true), { _, value -> outputs += value })
            }
            apply(listOf(field))
            assertTrue(outputs.isEmpty())
            apply(listOf(sibling))
            assertEquals(listOf(listOf(sibling)), outputs.flatMap { f.ops.leaves(it).map { leaf -> leaf.fact.path } })
            assertTrue(outputs.all { RuntimeDataDomain.base(it.base) })
        }
    }

    @Test fun `a constant conditional action is rejected without dropping its valid sibling action`() {
        MethodAnalysisFixtures().use { f ->
            val builder = RulePredicate.Builder(f.cancellation)
            val first = f.pattern(argument)
            val other = f.pattern(AccessPathBase.Argument(1))
            val predicate = builder.build(builder.and(listOf(builder.leaf(first), builder.leaf(other))))
            val id = RuleOccurrenceId(FormKey(FormOwner(), f.key.method, f.key, f.inst(1)),
                RuleKind.CALL_SOURCE, 0)
            val source = SourceRuleOccurrence(id, predicate, listOf(
                SourceAction(ActionId(id, ActionRole.SOURCE, 0), first.fact.copy(base = literal)),
                SourceAction(ActionId(id, ActionRole.SOURCE, 1), first.fact.copy(base = AccessPathBase.Return)),
            ))
            val core = f.core(localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val emitted = ArrayList<Pair<PremiseKey, Facts>>()
            for (pattern in listOf(first, other)) {
                val origin = f.manager.initial(pattern)
                core.localServices.sourcePredicate(source, origin, f.fact(pattern.fact.base), f.inst(1), false) { pr, value ->
                    emitted += pr to value
                }
            }
            assertEquals(2, emitted.size, "Both complete run-1 origins retain the valid action")
            assertTrue(emitted.all { it.second.base == AccessPathBase.Return })
        }
    }

    @Test fun `constant source transfer does not execute a source hook in either direction`() {
        for (index in listOf(2, 3)) MethodAnalysisFixtures().use { f ->
            val core = f.core(index = index)
            val target = PathFact(literal, emptyList(), Tail.EXACT, MarkSlot.Concrete(f.mark("T")))
            val source = MicroEdge.of(PathEdge(ZERO_FACT, target, ExclusionSet.Empty))
            val directed = if (index == 2) MicroEdge(PathEdge(target, ZERO_FACT, ExclusionSet.Empty), source.forward) else source
            val premise = if (index == 2)
                f.manager.initial(target.base, null, target.tail, ExclusionSet.Empty, target.mark) else f.manager.zero
            val input = if (index == 2) f.fact(literal) else Reach.NORMAL
            core.applier.statement(StatementSummary(setOf(input.base), listOf(directed), emptyList(), emptyMap()),
                premise, input, Place(f.inst(1), statementEdge = false, sources = true), { _, _ ->
                    fail("A constant source cannot produce executable data")
                })
            assertTrue(core.sourceHits?.occurrences()?.none() ?: true)
        }
    }
}
