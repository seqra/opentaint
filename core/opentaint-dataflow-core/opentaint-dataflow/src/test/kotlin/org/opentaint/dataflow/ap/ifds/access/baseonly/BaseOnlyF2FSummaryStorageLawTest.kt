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
    private val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled)
    private val entryPoint by lazy { MethodEntryPoint(EmptyMethodContext, inst) }
    private val exA = ExclusionSet.Concrete(TaintMarkAccessor("excluded-a"))
    private val exB = ExclusionSet.Concrete(TaintMarkAccessor("excluded-b"))

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

        manager.enableNormalizedEdges()
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

        manager.enableNormalizedEdges()
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
    fun `nonidentity exclusion aggregation is intersection and insertion-order independent`() {
        val field = field("aggregate")
        val initial = packBaseOnlyAccess(NO_ACCESSOR, field, ABSTRACT_MARK)
        val finalA = packBaseOnlyAccess(NO_ACCESSOR, field, mark("aggregate-a"))
        val finalB = packBaseOnlyAccess(NO_ACCESSOR, field, mark("aggregate-b"))

        fun run(edges: List<Edge.FactToFact>): Set<Record> {
            val summaries = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager)
            val delta = mutableListOf<FactToFactEdgeBuilder>()
            summaries.add(edges, delta)
            assertEquals(2, delta.size)
            assertTrue(delta.all { it.record().exclusion == ExclusionSet.Empty })
            return summaries.records().toSet()
        }

        val forward = run(listOf(edge(initial, finalA, exA), edge(initial, finalB, exB)))
        val reverse = run(listOf(edge(initial, finalB, exB), edge(initial, finalA, exA)))

        assertEquals(forward, reverse)
        assertEquals(setOf(finalA, finalB), forward.mapTo(hashSetOf()) { it.final })
        assertTrue(forward.all { it.exclusion == ExclusionSet.Empty })
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
    fun `concurrent nonidentity publication never pairs a new final with the old aggregate exclusion`() {
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
                        val records = observed.map(::record)
                        if (records.any { it.final != firstFinal }) {
                            assertTrue(
                                records.all { it.exclusion == ExclusionSet.Empty },
                                "a newly published final was observed with the pre-merge exclusion",
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
        assertTrue(eventual.all { record(it).exclusion == ExclusionSet.Empty })
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
