package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.CountDownLatch
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class BaseOnlyF2FSummaryStorageLawTest {
    private val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, Cancellation())
    private val entryPoint by lazy { MethodEntryPoint(EmptyMethodContext, inst) }
    private val exA = ExclusionSet.Concrete(TaintMarkAccessor("excluded-a"))
    private val exB = ExclusionSet.Concrete(TaintMarkAccessor("excluded-b"))
    private val exC = ExclusionSet.Concrete(TaintMarkAccessor("excluded-c"))

    @Test
    fun `normalized alias emits no delta and reads the primary exclusion`() {
        val summaries = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager)
        val initial = packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)
        val normalized = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, ABSTRACT_MARK)
        val final = packBaseOnlyAccess(NO_ACCESSOR, field("field"), ABSTRACT_MARK)

        val firstDelta = mutableListOf<FactToFactEdgeBuilder>()
        summaries.add(listOf(edge(initial, final, exA)), firstDelta)
        assertEquals(listOf(exA), firstDelta.map { it.record().exclusion })

        val secondDelta = mutableListOf<FactToFactEdgeBuilder>()
        summaries.add(listOf(edge(initial, final, exB)), secondDelta)
        assertEquals(listOf(ExclusionSet.Empty), secondDelta.map { it.record().exclusion })

        manager.enableTraceResolutionMode()
        val records = summaries.records()
        assertEquals(2, records.size)
        assertEquals(
            setOf(initial, normalized),
            records.mapTo(hashSetOf()) { it.initial },
            "the alias is a query view, not a second insertion delta",
        )
        assertTrue(records.all { it.exclusion == ExclusionSet.Empty })
    }

    @Test
    fun `normalized alias and exact primary merge as one logical view`() {
        val summaries = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager)
        val original = packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)
        val normalized = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, ABSTRACT_MARK)
        val final = packBaseOnlyAccess(NO_ACCESSOR, field("field-2"), ABSTRACT_MARK)
        val added = mutableListOf<FactToFactEdgeBuilder>()

        summaries.add(listOf(edge(original, final, exA), edge(normalized, final, exB)), added)
        assertEquals(2, added.size, "both primary aggregates contribute insertion deltas")

        manager.enableTraceResolutionMode()
        val records = summaries.records()
        assertEquals(2, records.size, "the alias must not duplicate the exact primary view")
        assertEquals(exA, records.single { it.initial == original }.exclusion)
        assertEquals(
            ExclusionSet.Empty,
            records.single { it.initial == normalized }.exclusion,
            "alternative alias/primary exclusions merge by intersection",
        )
    }

    @Test
    fun `repeated same-key updates in one batch emit one committed aggregate`() {
        val summaries = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager)
        val field = field("batch")
        val initial = packBaseOnlyAccess(NO_ACCESSOR, field, ABSTRACT_MARK)
        val final = packBaseOnlyAccess(NO_ACCESSOR, field, mark("batch-final"))
        val added = mutableListOf<FactToFactEdgeBuilder>()

        summaries.add(listOf(edge(initial, final, exA), edge(initial, final, exB)), added)

        assertEquals(1, added.size)
        assertEquals(ExclusionSet.Empty, added.single().record().exclusion)
        assertEquals(listOf(ExclusionSet.Empty), summaries.records().map { it.exclusion })
    }

    @Test
    fun `rejected transient summary has no observable partition or delta`() {
        val summaries = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager)
        val initial = packBaseOnlyAccess(NO_ACCESSOR, field("valid-initial"), ABSTRACT_MARK)
        val collapsed = packBaseOnlyAccess(NO_ACCESSOR, field("transient-final"), COLLAPSED_MARK)
        val invalid = edge(initial, collapsed, exA)
        val rejectedDelta = mutableListOf<FactToFactEdgeBuilder>()

        summaries.add(listOf(invalid), rejectedDelta)
        assertTrue(rejectedDelta.isEmpty())
        assertTrue(summaries.records().isEmpty())

        val final = packBaseOnlyAccess(NO_ACCESSOR, field("valid-final"), mark("valid-mark"))
        val acceptedDelta = mutableListOf<FactToFactEdgeBuilder>()
        summaries.add(listOf(edge(initial, final, exA)), acceptedDelta)
        assertEquals(1, acceptedDelta.size)
        assertEquals(1, summaries.records().size)
    }

    @Test
    fun `different finals keep independent exclusions in either insertion order`() {
        val field = field("aggregate")
        val initial = packBaseOnlyAccess(NO_ACCESSOR, field, ABSTRACT_MARK)
        val finalA = packBaseOnlyAccess(NO_ACCESSOR, field, mark("aggregate-a"))
        val finalB = packBaseOnlyAccess(NO_ACCESSOR, field, mark("aggregate-b"))

        fun run(edges: List<Edge.FactToFact>): Set<Record> {
            val summaries = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager)
            val delta = mutableListOf<FactToFactEdgeBuilder>()
            summaries.add(edges, delta)
            assertEquals(2, delta.size)
            return summaries.records().toSet()
        }

        val forward = run(listOf(edge(initial, finalA, exA), edge(initial, finalB, exB)))
        val reverse = run(listOf(edge(initial, finalB, exB), edge(initial, finalA, exA)))

        assertEquals(forward, reverse)
        assertEquals(
            setOf(
                Record(initial, finalA, exA),
                Record(initial, finalB, exB),
            ),
            forward,
        )
    }

    @Test
    fun `identity cross-slot records remain distinct in both insertion orders`() {
        val suffix = manager.interner.index(TaintMarkAccessor("identity-suffix"))
        val noField = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, suffix)
        val fieldAp = packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)

        fun run(first: BaseOnlyAccess, second: BaseOnlyAccess): Pair<List<Record>, List<Record>> {
            val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
            val delta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.add(listOf(storageEdge(first, first), storageEdge(second, second)), delta)
            val current = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.collectSummariesTo(current, null)
            return delta.map(::record) to current.map(::record)
        }

        for ((first, second) in listOf(noField to fieldAp, fieldAp to noField)) {
            val (delta, current) = run(first, second)
            assertEquals(setOf(noField, fieldAp), delta.mapTo(hashSetOf()) { it.initial }, "delta order $first then $second")
            assertEquals(setOf(noField, fieldAp), current.mapTo(hashSetOf()) { it.initial }, "state order $first then $second")
        }
    }

    @Test
    fun `identity abstraction suppresses only permitted same-slot children in both insertion orders`() {
        val markAccessor = TaintMarkAccessor("identity-child")
        val suffix = manager.interner.index(markAccessor)
        val abstract = ABSTRACT_EMPTY_ACCESS
        val normal = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, suffix, BaseOnlyValueAccessorState.Normal)
        val value = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, suffix, BaseOnlyValueAccessorState.Value)

        fun run(edges: List<CommonF2FSummary.StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>): Set<BaseOnlyAccess> {
            val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
            val delta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.add(edges, delta)
            val current = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.collectSummariesTo(current, null)
            assertEquals(current.mapTo(hashSetOf()) { record(it).initial }, delta.mapTo(hashSetOf()) { record(it).initial })
            return current.mapTo(hashSetOf()) { record(it).initial }
        }

        val abstractEdge = storageEdge(abstract, abstract, ExclusionSet.Empty)
        val normalEdge = storageEdge(normal, normal, ExclusionSet.Empty)
        val valueEdge = storageEdge(value, value, ExclusionSet.Empty)
        assertEquals(setOf(abstract), run(listOf(normalEdge, valueEdge, abstractEdge)))
        assertEquals(setOf(abstract), run(listOf(abstractEdge, normalEdge, valueEdge)))

        val excludingAbstract = storageEdge(
            abstract,
            abstract,
            ExclusionSet.Concrete(markAccessor),
        )
        assertEquals(
            setOf(abstract, normal, value),
            run(listOf(excludingAbstract, normalEdge, valueEdge)),
            "an excluded child must remain explicit, including both value-accessor states",
        )
    }

    @Test
    fun `value accessor states remain distinct summary keys`() {
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
        val suffix = mark("mode-key")
        val final = packBaseOnlyAccess(NO_ACCESSOR, field("mode-final"), mark("mode-result"))
        val initials = BaseOnlyValueAccessorState.entries.map { state ->
            packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, suffix, state)
        }
        storage.add(initials.map { storageEdge(it, final) }, mutableListOf())

        fun query(pattern: BaseOnlyAccess?): Set<BaseOnlyAccess> {
            val result = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.collectSummariesTo(result, pattern)
            return result.mapTo(hashSetOf()) { record(it).initial }
        }

        assertEquals(initials.toSet(), query(null))
        val normal = initials[BaseOnlyValueAccessorState.Normal.ordinal]
        val value = initials[BaseOnlyValueAccessorState.Value.ordinal]
        assertEquals(setOf(normal), query(normal))
        assertEquals(setOf(value), query(value))
    }

    @Test
    fun `correlated abstract edge subsumes its concrete specialization`() {
        val fieldA = field("subsumption-a")
        val fieldB = field("subsumption-b")
        val terminal = mark("subsumption-mark")
        val broad = BaseOnlySummaryEdge(
            initial = packBaseOnlyAccess(NO_ACCESSOR, fieldA, ABSTRACT_MARK),
            final = packBaseOnlyAccess(NO_ACCESSOR, fieldB, ABSTRACT_MARK),
            exclusion = ExclusionSet.Empty,
        )
        val narrow = BaseOnlySummaryEdge(
            initial = packBaseOnlyAccess(NO_ACCESSOR, fieldA, terminal),
            final = packBaseOnlyAccess(NO_ACCESSOR, fieldB, terminal),
            exclusion = ExclusionSet.Empty,
        )

        assertTrue(BaseOnlySummaryEdgeOps.subsumes(manager, broad, narrow))
        assertFalse(BaseOnlySummaryEdgeOps.subsumes(manager, narrow, broad))
    }

    @Test
    fun `correlated abstract edge does not subsume a different final residual`() {
        val fieldA = field("mismatch-a")
        val fieldB = field("mismatch-b")
        val broad = BaseOnlySummaryEdge(
            initial = packBaseOnlyAccess(NO_ACCESSOR, fieldA, ABSTRACT_MARK),
            final = packBaseOnlyAccess(NO_ACCESSOR, fieldB, ABSTRACT_MARK),
            exclusion = ExclusionSet.Empty,
        )
        val mismatch = BaseOnlySummaryEdge(
            initial = packBaseOnlyAccess(NO_ACCESSOR, fieldA, mark("mismatch-in")),
            final = packBaseOnlyAccess(NO_ACCESSOR, fieldB, mark("mismatch-out")),
            exclusion = ExclusionSet.Empty,
        )

        assertFalse(BaseOnlySummaryEdgeOps.subsumes(manager, broad, mismatch))
    }

    @Test
    fun `same premise with abstract conclusion subsumes a concrete field conclusion`() {
        val premise = packBaseOnlyAccess(NO_ACCESSOR, field("premise-field"), ABSTRACT_MARK)
        val abstractConclusion = BaseOnlySummaryEdge(
            initial = premise,
            final = ABSTRACT_EMPTY_ACCESS,
            exclusion = ExclusionSet.Empty,
        )
        val concreteConclusion = BaseOnlySummaryEdge(
            initial = premise,
            final = packBaseOnlyAccess(NO_ACCESSOR, field("conclusion-field"), ABSTRACT_MARK),
            exclusion = ExclusionSet.Empty,
        )

        assertTrue(BaseOnlySummaryEdgeOps.subsumes(manager, abstractConclusion, concreteConclusion))
        assertFalse(BaseOnlySummaryEdgeOps.subsumes(manager, concreteConclusion, abstractConclusion))
    }

    @Test
    fun `summary antichain keeps the abstract conclusion for a shared premise in either order`() {
        val premise = packBaseOnlyAccess(NO_ACCESSOR, field("antichain-premise"), ABSTRACT_MARK)
        val abstractConclusion = storageEdge(
            initial = premise,
            final = ABSTRACT_EMPTY_ACCESS,
        )
        val concreteConclusion = storageEdge(
            initial = premise,
            final = packBaseOnlyAccess(NO_ACCESSOR, field("antichain-conclusion"), ABSTRACT_MARK),
        )

        fun run(edges: List<CommonF2FSummary.StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>): Set<Record> {
            val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
            storage.add(edges, mutableListOf())
            val current = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.collectSummariesTo(current, null)
            return current.mapTo(hashSetOf(), ::record)
        }

        val expected = setOf(Record(premise, ABSTRACT_EMPTY_ACCESS, ExclusionSet.Empty))
        assertEquals(expected, run(listOf(abstractConclusion, concreteConclusion)))
        assertEquals(expected, run(listOf(concreteConclusion, abstractConclusion)))
    }

    @Test
    fun `same premise conclusion subsumption preserves exclusion ordering`() {
        val premise = packBaseOnlyAccess(NO_ACCESSOR, field("exclusion-premise"), ABSTRACT_MARK)
        val generalWithExclusion = BaseOnlySummaryEdge(
            initial = premise,
            final = ABSTRACT_EMPTY_ACCESS,
            exclusion = exA,
        )
        val specificWithoutExclusion = BaseOnlySummaryEdge(
            initial = premise,
            final = packBaseOnlyAccess(NO_ACCESSOR, field("exclusion-conclusion"), ABSTRACT_MARK),
            exclusion = ExclusionSet.Empty,
        )
        val generalWithoutExclusion = generalWithExclusion.copy(exclusion = ExclusionSet.Empty)
        val specificWithExclusion = specificWithoutExclusion.copy(exclusion = exA)

        assertFalse(BaseOnlySummaryEdgeOps.subsumes(manager, generalWithExclusion, specificWithoutExclusion))
        assertTrue(BaseOnlySummaryEdgeOps.subsumes(manager, generalWithoutExclusion, specificWithExclusion))
    }

    @Test
    fun `excluded residual prevents summary edge subsumption`() {
        val fieldA = field("excluded-a")
        val fieldB = field("excluded-b")
        val markAccessor = TaintMarkAccessor("excluded-residual")
        val terminal = manager.interner.index(markAccessor)
        val broad = BaseOnlySummaryEdge(
            initial = packBaseOnlyAccess(NO_ACCESSOR, fieldA, ABSTRACT_MARK),
            final = packBaseOnlyAccess(NO_ACCESSOR, fieldB, ABSTRACT_MARK),
            exclusion = ExclusionSet.Concrete(markAccessor),
        )
        val narrow = BaseOnlySummaryEdge(
            initial = packBaseOnlyAccess(NO_ACCESSOR, fieldA, terminal),
            final = packBaseOnlyAccess(NO_ACCESSOR, fieldB, terminal),
            exclusion = ExclusionSet.Empty,
        )

        assertFalse(BaseOnlySummaryEdgeOps.subsumes(manager, broad, narrow))
    }

    @Test
    fun `summary antichain keeps only broad correlated edge in either insertion order`() {
        val fieldA = field("antichain-a")
        val fieldB = field("antichain-b")
        val terminal = mark("antichain-mark")
        val broad = storageEdge(
            initial = packBaseOnlyAccess(NO_ACCESSOR, fieldA, ABSTRACT_MARK),
            final = packBaseOnlyAccess(NO_ACCESSOR, fieldB, ABSTRACT_MARK),
        )
        val narrow = storageEdge(
            initial = packBaseOnlyAccess(NO_ACCESSOR, fieldA, terminal),
            final = packBaseOnlyAccess(NO_ACCESSOR, fieldB, terminal),
        )

        fun run(edges: List<CommonF2FSummary.StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>): Set<Record> {
            val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
            val delta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.add(edges, delta)
            val current = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.collectSummariesTo(current, null)
            assertEquals(current.map(::record).toSet(), delta.map(::record).toSet())
            return current.mapTo(hashSetOf(), ::record)
        }

        val expected = setOf(Record(broad.initial, broad.final, ExclusionSet.Empty))
        assertEquals(expected, run(listOf(narrow, broad)))
        assertEquals(expected, run(listOf(broad, narrow)))
    }

    @Test
    fun `adding broad edge evicts published narrow edge and adding narrow edge is ignored`() {
        val fieldA = field("incremental-a")
        val fieldB = field("incremental-b")
        val terminal = mark("incremental-mark")
        val broad = storageEdge(
            initial = packBaseOnlyAccess(NO_ACCESSOR, fieldA, ABSTRACT_MARK),
            final = packBaseOnlyAccess(NO_ACCESSOR, fieldB, ABSTRACT_MARK),
        )
        val narrow = storageEdge(
            initial = packBaseOnlyAccess(NO_ACCESSOR, fieldA, terminal),
            final = packBaseOnlyAccess(NO_ACCESSOR, fieldB, terminal),
        )

        val narrowThenBroad = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
        narrowThenBroad.add(listOf(narrow), mutableListOf())
        val broadDelta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        narrowThenBroad.add(listOf(broad), broadDelta)
        assertEquals(setOf(broad.initial), broadDelta.mapTo(hashSetOf()) { record(it).initial })
        val afterEviction = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        narrowThenBroad.collectSummariesTo(afterEviction, null)
        assertEquals(setOf(broad.initial), afterEviction.mapTo(hashSetOf()) { record(it).initial })

        val broadThenNarrow = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
        broadThenNarrow.add(listOf(broad), mutableListOf())
        val ignoredDelta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        broadThenNarrow.add(listOf(narrow), ignoredDelta)
        assertTrue(ignoredDelta.isEmpty())
    }

    @Test
    fun `field generalization has a sixteen edge budget and monotone deltas`() {
        val members = (0 until 18).map { index ->
            storageEdge(
                initial = packBaseOnlyAccess(NO_ACCESSOR, field("budget-$index"), ABSTRACT_MARK),
                final = ABSTRACT_EMPTY_ACCESS,
                exclusion = if (index % 2 == 0) exA else exB,
            )
        }
        val representative = Record(
            initial = ABSTRACT_EMPTY_ACCESS,
            final = ABSTRACT_EMPTY_ACCESS,
            exclusion = exA.union(exB),
        )
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()

        val belowBudgetDelta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        storage.add(members.take(MAX_FIELD_ENUMERATION_EDGES), belowBudgetDelta)
        assertEquals(
            members.take(MAX_FIELD_ENUMERATION_EDGES)
                .mapTo(hashSetOf()) { Record(it.initial, it.final, it.exclusion) },
            belowBudgetDelta.mapTo(hashSetOf(), ::record),
        )

        val crossingDelta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        storage.add(listOf(members[MAX_FIELD_ENUMERATION_EDGES]), crossingDelta)
        assertEquals(listOf(representative), crossingDelta.map(::record))

        val afterCrossing = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        storage.collectSummariesTo(afterCrossing, null)
        assertEquals(listOf(representative), afterCrossing.map(::record))

        val absorbed = members[MAX_FIELD_ENUMERATION_EDGES + 1].copy(exclusion = exC)
        val absorbedDelta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        storage.add(listOf(absorbed), absorbedDelta)
        val representativeWithAbsorbedExclusion = representative.copy(
            exclusion = exA.union(exB).union(exC),
        )
        assertEquals(
            listOf(representativeWithAbsorbedExclusion),
            absorbedDelta.map(::record),
            "a later member must update the representative without re-enumerating the group",
        )

        val afterAbsorption = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        storage.collectSummariesTo(afterAbsorption, null)
        assertEquals(listOf(representativeWithAbsorbedExclusion), afterAbsorption.map(::record))

        val repeatedDelta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        storage.add(listOf(absorbed), repeatedDelta)
        assertTrue(repeatedDelta.isEmpty(), "an unchanged generalized representative emits no delta")
    }

    @Test
    fun `field generalization can be disabled`() {
        val exactManager = BaseOnlyApManager(
            AnyAccessorUnrollStrategy.AnyAccessorDisabled,
            Cancellation(),
            fieldGeneralizationEnabled = false,
        )
        val members = (0 until MAX_FIELD_ENUMERATION_EDGES + 2).map { index ->
            storageEdge(
                initial = packBaseOnlyAccess(
                    NO_ACCESSOR,
                    exactManager.interner.index(FieldAccessor("Owner", "exact-$index", "Value")),
                    ABSTRACT_MARK,
                ),
                final = ABSTRACT_EMPTY_ACCESS,
                exclusion = if (index % 2 == 0) exA else exB,
            )
        }
        val expected = members.mapTo(hashSetOf()) {
            Record(it.initial, it.final, it.exclusion)
        }
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, exactManager).createStorage()
        val delta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()

        storage.add(members, delta)
        exactManager.enableTraceResolutionMode()
        val current = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        storage.collectSummariesTo(current, null)

        assertEquals(expected, delta.mapTo(hashSetOf(), ::record))
        assertEquals(expected, current.mapTo(hashSetOf(), ::record))
        assertFalse(current.map(::record).any {
            it.initial == ABSTRACT_EMPTY_ACCESS && it.final == ABSTRACT_EMPTY_ACCESS
        })
    }

    @Test
    fun `field generalization is invariant under insertion order`() {
        val members = (0..MAX_FIELD_ENUMERATION_EDGES).map { index ->
            storageEdge(
                initial = packBaseOnlyAccess(NO_ACCESSOR, field("order-$index"), ABSTRACT_MARK),
                final = ABSTRACT_EMPTY_ACCESS,
                exclusion = if (index % 2 == 0) exA else exB,
            )
        }
        val representative = Record(
            initial = ABSTRACT_EMPTY_ACCESS,
            final = ABSTRACT_EMPTY_ACCESS,
            exclusion = exA.union(exB),
        )
        val orders = buildList {
            add(members)
            add(members.reversed())
            for (shift in listOf(1, 5, 11)) {
                add(members.drop(shift) + members.take(shift))
            }
        }

        orders.forEachIndexed { orderIndex, order ->
            val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
            val delta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.add(order, delta)
            val current = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.collectSummariesTo(current, null)

            assertEquals(listOf(representative), delta.map(::record), "delta for order $orderIndex")
            assertEquals(listOf(representative), current.map(::record), "state for order $orderIndex")
        }
    }

    @Test
    fun `static semantic and value dimensions are excluded from field generalization`() {
        fun assertRetained(
            scenario: String,
            edges: List<CommonF2FSummary.StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>,
        ) {
            val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
            val delta = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.add(edges, delta)
            val current = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.collectSummariesTo(current, null)
            val expected = edges.mapTo(hashSetOf()) { Record(it.initial, it.final, it.exclusion) }
            assertEquals(expected, delta.mapTo(hashSetOf(), ::record), "$scenario delta")
            assertEquals(expected, current.mapTo(hashSetOf(), ::record), "$scenario state")
        }

        val staticInitial = static("non-generalized-initial-static")
        assertRetained(
            "initial static",
            (0..MAX_FIELD_ENUMERATION_EDGES).map { index ->
                storageEdge(
                    packBaseOnlyAccess(staticInitial, field("static-in-$index"), ABSTRACT_MARK),
                    ABSTRACT_EMPTY_ACCESS,
                )
            },
        )

        val staticFinal = static("non-generalized-final-static")
        assertRetained(
            "final static",
            (0..MAX_FIELD_ENUMERATION_EDGES).map { index ->
                storageEdge(
                    packBaseOnlyAccess(NO_ACCESSOR, field("static-out-$index"), ABSTRACT_MARK),
                    packBaseOnlyAccess(staticFinal, NO_ACCESSOR, ABSTRACT_MARK),
                )
            },
        )

        val initialSemantic = mark("non-generalized-initial-semantic")
        assertRetained(
            "initial semantic",
            (0..MAX_FIELD_ENUMERATION_EDGES).map { index ->
                storageEdge(
                    packBaseOnlyAccess(NO_ACCESSOR, field("semantic-in-$index"), initialSemantic),
                    ABSTRACT_EMPTY_ACCESS,
                )
            },
        )

        val finalSemantic = mark("non-generalized-final-semantic")
        assertRetained(
            "final semantic and value mode",
            (0..MAX_FIELD_ENUMERATION_EDGES).flatMap { index ->
                val initial = packBaseOnlyAccess(NO_ACCESSOR, field("semantic-out-$index"), ABSTRACT_MARK)
                BaseOnlyValueAccessorState.entries.map { state ->
                    storageEdge(
                        initial,
                        packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, finalSemantic, state),
                    )
                }
            },
        )
    }

    @Test
    fun `pattern filtering finds the generalized edge for every removed premise`() {
        val structuralAccessors = listOf(ELEMENT_ACCESSOR_IDX) +
            (0 until MAX_FIELD_ENUMERATION_EDGES).map { index -> field("pattern-generalized-$index") }
        val members = structuralAccessors.map { accessor ->
            storageEdge(
                initial = packBaseOnlyAccess(NO_ACCESSOR, accessor, ABSTRACT_MARK),
                final = if (accessor == ELEMENT_ACCESSOR_IDX) {
                    packBaseOnlyAccess(NO_ACCESSOR, ELEMENT_ACCESSOR_IDX, ABSTRACT_MARK)
                } else {
                    ABSTRACT_EMPTY_ACCESS
                },
            )
        }
        val representative = Record(
            initial = ABSTRACT_EMPTY_ACCESS,
            final = ABSTRACT_EMPTY_ACCESS,
            exclusion = ExclusionSet.Empty,
        )
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
        storage.add(members, mutableListOf())

        members.forEach { member ->
            val queried = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.collectSummariesTo(queried, member.initial)
            assertEquals(
                listOf(representative),
                queried.map(::record),
                "removed premise ${member.initial} must select its generalized representative",
            )
        }

        manager.enableTraceResolutionMode()
        val all = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        storage.collectSummariesTo(all, null)
        assertEquals(listOf(representative), all.map(::record), "normalized views must not duplicate the representative")
    }

    @Test
    fun `concurrent first-leaf publication never exposes synthetic Universe exclusion`() {
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
        val failures = ConcurrentLinkedQueue<Throwable>()
        val started = CountDownLatch(1)
        val finished = AtomicBoolean(false)
        val executor = Executors.newFixedThreadPool(4)
        val exclusion = ExclusionSet.Concrete(TaintMarkAccessor("real-exclusion"))
        val count = 2_000

        executor.submit {
            try {
                started.countDown()
                repeat(count) { index ->
                    val suffix = manager.interner.index(TaintMarkAccessor("leaf-$index"))
                    val access = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, suffix)
                    storage.add(listOf(storageEdge(access, access, exclusion)), mutableListOf())
                }
            } catch (t: Throwable) {
                failures += t
            } finally {
                finished.set(true)
            }
        }
        repeat(3) {
            executor.submit {
                try {
                    started.await()
                    while (!finished.get()) {
                        val observed = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
                        storage.collectSummariesTo(observed, null)
                        observed.forEach { builder ->
                            assertFalse(record(builder).exclusion is ExclusionSet.Universe)
                        }
                    }
                } catch (t: Throwable) {
                    failures += t
                }
            }
        }

        executor.shutdown()
        assertTrue(executor.awaitTermination(30, TimeUnit.SECONDS))
        assertTrue(failures.isEmpty(), failures.joinToString("\n"))

        val eventual = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        storage.collectSummariesTo(eventual, null)
        assertEquals(count, eventual.size)
        assertTrue(eventual.all { record(it).exclusion == exclusion })
    }

    @Test
    fun `concurrent publication preserves each final exclusion`() {
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
        val initial = packBaseOnlyAccess(NO_ACCESSOR, field("publication"), ABSTRACT_MARK)
        val firstFinal = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, mark("publication-first"))
        storage.add(listOf(storageEdge(initial, firstFinal, exA)), mutableListOf())

        val failures = ConcurrentLinkedQueue<Throwable>()
        val started = CountDownLatch(1)
        val finished = AtomicBoolean(false)
        val executor = Executors.newFixedThreadPool(4)
        val count = 2_000

        executor.submit {
            try {
                started.countDown()
                repeat(count) { index ->
                    val final = packBaseOnlyAccess(
                        NO_ACCESSOR,
                        NO_ACCESSOR,
                        manager.interner.index(TaintMarkAccessor("publication-$index")),
                    )
                    storage.add(listOf(storageEdge(initial, final, exB)), mutableListOf())
                }
            } catch (t: Throwable) {
                failures += t
            } finally {
                finished.set(true)
            }
        }
        repeat(3) {
            executor.submit {
                try {
                    started.await()
                    while (!finished.get()) {
                        val observed = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
                        storage.collectSummariesTo(observed, null)
                        observed.map(::record).forEach { record ->
                            assertEquals(
                                if (record.final == firstFinal) exA else exB,
                                record.exclusion,
                                "a final was observed with another edge's exclusion",
                            )
                        }
                    }
                } catch (t: Throwable) {
                    failures += t
                }
            }
        }

        executor.shutdown()
        assertTrue(executor.awaitTermination(30, TimeUnit.SECONDS))
        assertTrue(failures.isEmpty(), failures.joinToString("\n"))

        val eventual = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        storage.collectSummariesTo(eventual, null)
        assertEquals(count + 1, eventual.size)
        eventual.map(::record).forEach { record ->
            assertEquals(if (record.final == firstFinal) exA else exB, record.exclusion)
        }
    }

    @Test
    fun `patterned query equals a scan-and-predicate reference`() {
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager).createStorage()
        val fieldA = field("query-a")
        val fieldB = field("query-b")
        val static = static("query-static")
        val initials = listOf(
            packBaseOnlyAccess(NO_ACCESSOR, fieldA, ABSTRACT_MARK),
            packBaseOnlyAccess(NO_ACCESSOR, fieldB, ABSTRACT_MARK),
            packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, ABSTRACT_MARK),
            packBaseOnlyAccess(static, fieldA, ABSTRACT_MARK),
        )
        val inserted = buildList {
            initials.forEachIndexed { index, initial ->
                add(storageEdge(initial, packBaseOnlyAccess(initial.staticIdx, initial.fieldIdx, mark("query-a-$index")), exA))
                add(storageEdge(initial, packBaseOnlyAccess(initial.staticIdx, initial.fieldIdx, mark("query-b-$index")), exB))
            }
        }
        storage.add(inserted, mutableListOf())

        val all = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
        storage.collectSummariesTo(all, null)
        val scan = all.map(::record)
        val patterns = initials + listOf(
            packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR),
            packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR),
        )

        for (pattern in patterns) {
            val expected = scan.filter { baseOnlySummaryInitialMatches(pattern, it.initial) }.toSet()
            val queried = mutableListOf<CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>()
            storage.collectSummariesTo(queried, pattern)
            assertEquals(expected, queried.map(::record).toSet(), "pattern=$pattern")
        }
    }

    private fun edge(initial: BaseOnlyAccess, final: BaseOnlyAccess, exclusion: ExclusionSet): Edge.FactToFact =
        Edge.FactToFact(
            entryPoint,
            BaseOnlyInitialFactAp(manager, AccessPathBase.This, initial, exclusion),
            inst,
            BaseOnlyFinalFactAp(manager, AccessPathBase.Return, final, exclusion),
        )

    private fun field(name: String): Int =
        manager.interner.index(FieldAccessor("C", name, "T"))

    private fun mark(name: String): Int =
        manager.interner.index(TaintMarkAccessor(name))

    private fun static(name: String): Int =
        manager.interner.index(ClassStaticAccessor(name))

    private fun storageEdge(
        initial: BaseOnlyAccess,
        final: BaseOnlyAccess,
        exclusion: ExclusionSet = ExclusionSet.Empty,
    ) = CommonF2FSummary.StorageEdge(initial, final, exclusion)

    private fun MethodInitialToFinalBaseOnlyApSummariesStorage.records(): List<Record> {
        val builders = mutableListOf<FactToFactEdgeBuilder>()
        filterEdgesTo(builders, initialFactPattern = null, finalFactBase = AccessPathBase.Return)
        return builders.map { it.record() }
    }

    private fun FactToFactEdgeBuilder.record(): Record {
        val edge = setEntryPoint(entryPoint).build()
        return Record(
            (edge.initialFactAp as BaseOnlyInitialFactAp).access,
            (edge.factAp as BaseOnlyFinalFactAp).access,
            edge.initialFactAp.exclusions,
        )
    }

    private fun record(
        builder: CommonF2FSummary.F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>,
    ): Record {
        val edge = builder
            .setInitialFactBase(AccessPathBase.This)
            .setExitFactBase(AccessPathBase.Return)
            .build()
            .setEntryPoint(entryPoint)
            .setExitStatement(inst)
            .build()
        return Record(
            (edge.initialFactAp as BaseOnlyInitialFactAp).access,
            (edge.factAp as BaseOnlyFinalFactAp).access,
            edge.initialFactAp.exclusions,
        )
    }

    private data class Record(
        val initial: BaseOnlyAccess,
        val final: BaseOnlyAccess,
        val exclusion: ExclusionSet,
    )

    private val method: CommonMethod = object : CommonMethod {
        override val name: String = "baseOnlyF2FStorageLaws"
        override val parameters: List<CommonMethodParameter> = emptyList()
        override val returnType: CommonTypeName = object : CommonTypeName {
            override val typeName: String = "java.lang.Object"
        }

        override fun flowGraph(): ControlFlowGraph<CommonInst> = object : ControlFlowGraph<CommonInst> {
            override val instructions: List<CommonInst> = emptyList()
            override val entries: List<CommonInst> = emptyList()
            override val exits: List<CommonInst> = emptyList()
            override fun successors(node: CommonInst): Set<CommonInst> = emptySet()
            override fun predecessors(node: CommonInst): Set<CommonInst> = emptySet()
        }
    }

    private val inst: CommonInst = object : CommonInst {
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val method: CommonMethod get() = this@BaseOnlyF2FSummaryStorageLawTest.method
        }
    }
}
