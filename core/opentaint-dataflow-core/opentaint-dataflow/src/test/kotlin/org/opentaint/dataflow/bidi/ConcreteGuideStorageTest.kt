package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.projectBlockHandOff
import org.opentaint.dataflow.bidi.engine.NeutralRelationBatch
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** Native leaves are the oracle; a mixed wrapper is not a scalar tail/E. */
internal data class StorageCoordinateSnapshot(val ordinary: Set<Conclusion>, val flags: Set<Conclusion>)

/** Build a literal packet without scalar normalization. All supplied ANY
 * conclusions are DEMAND; NORMAL ANY has no legal scalar observation (W6). */
internal fun StoreValues.rawStoragePacket(vararg atoms: Conclusion): TaintTree {
    require(atoms.isNotEmpty())
    val first = atoms.first()
    require(atoms.all { it.fact.base == first.fact.base && it.demand == first.demand })
    val spans = atoms.filter { it.fact.tail != Tail.EXACT }
    val span = spans.firstOrNull()
    require(spans.all { it.fact.tail == span!!.fact.tail && it.exclusion == span.exclusion })
    require(span == null || span.fact.tail != Tail.ANY || span.exclusion == ExclusionSet.Empty)
    val root = atoms.map { atom ->
        val mark = (atom.fact.mark as MarkSlot.Concrete).mark
        val marks = m.markSetOf(mark)
        val leaf = if (atom.fact.tail == Tail.EXACT) m.taintLeaves(marks, MarkSet.EMPTY)
            else m.taintLeaves(MarkSet.EMPTY, marks)
        m.taintAlg.prepend(m, m.path(atom.fact.path), m.taintAlg.leafNode(leaf))
    }.reduce { a, b -> m.taintAlg.mergeAdd(a, b, m.cancellation) }
    return m.taintTree(first.fact.base, if (first.demand) Layer.DEMAND else Layer.NORMAL, root,
        span?.exclusion ?: ExclusionSet.Empty, span?.fact?.tail ?: Tail.ANY_TAINT)
}

internal fun StoreValues.storageCoordinates(values: Iterable<Facts>): StorageCoordinateSnapshot {
    fun coordinates(value: Facts): List<Conclusion> = fixture.ops.leaves(value).map {
        Conclusion(it.fact, if (it.fact.tail == Tail.EXACT) ExclusionSet.Empty else it.exclusion,
            value.layer == Layer.DEMAND)
    }.toList()
    val current = values.toList()
    return StorageCoordinateSnapshot(current.flatMap(::coordinates).toSet(), current.flatMap { value ->
        (value as? TaintTree)?.protectedPart()?.let(::coordinates).orEmpty()
    }.toSet())
}

internal fun StoreValues.storageCoordinateRows(rows: Sequence<Pair<PremiseKey, Facts>>) =
    rows.toList().groupBy({ it.first }, { it.second }).mapValues { storageCoordinates(it.value) }

internal fun StoreValues.coordinatePacket(paths: List<List<Int>>, protected: Boolean = false,
                                         atoms: List<TaintMark> = listOf(t), tail: Tail = Tail.ANY,
                                         layer: Layer = Layer.DEMAND,
                                         e: ExclusionSet = ExclusionSet.Empty): DiagonalDelta {
    require(tail != Tail.ANY || layer == Layer.DEMAND) { "Packed ANY fixture uses the native DEMAND grammar" }
    val geometry = paths.map { FlowAlgebra.prepend(m, m.path(it), FlowAlgebra.LEAF_NODE) }
        .reduce { a, b -> FlowAlgebra.mergeAdd(a, b, m.cancellation) }
    return DiagonalDelta(premise(tail = Tail.STAR, mark = MarkSlot.STAR), y, layer, geometry,
        m.intern(MarkSet(atoms.map { it.id }.toIntArray())), protected, tail, e)
}

internal fun StoreValues.decodeCoordinates(packet: DiagonalDelta): List<Pair<PremiseKey, Facts>> =
    checkNotNull(NeutralRelationBatch.fromDiagonal(m, packet)).decode().map { (initial, facts) ->
        (initial as PremiseKey) to (facts as Facts)
    }.toList()

/** A rejected fast path must leave the complete current relation unchanged. */
internal fun StoreValues.admitCoordinatePacket(store: DiagonalRelations,
                                               packet: DiagonalDelta): List<Pair<PremiseKey, Facts>> {
    val before = storageCoordinateRows(store.all())
    val census = store.census()
    val admitted = store.addDiagonal(packet)
    if (admitted != null) return admitted.flatMap { decodeCoordinates(it) }
    assertEquals(before, storageCoordinateRows(store.all()), "Fallback must precede state mutation")
    assertEquals(census, store.census(), "Fallback must precede mask mutation")
    return decodeCoordinates(packet).flatMap { (initial, facts) ->
        store.addAll(initial, facts).map { initial to it }
    }
}

class ConcreteGuideStorageTest {
    private val fixture = StoreFixtures()
    private val v = StoreValues(fixture)

    @Test fun `cold concrete demand ANY keeps explicit heads but old exact pruning remains`() = with(v) {
        val guides = listOf(leaf(p(), Tail.ANY, layer = Layer.DEMAND),
            leaf(p(f), Tail.ANY, layer = Layer.DEMAND), leaf(p(f, g), Tail.ANY, layer = Layer.DEMAND))
        val coveredExact = leaf(p(f, g), Tail.EXACT, layer = Layer.DEMAND)
        val otherExact = leaf(p(g), Tail.EXACT, mu, Layer.DEMAND)
        val offered = pack(*(guides + coveredExact + otherExact).toTypedArray()) as TaintTree
        val expected = StorageCoordinateSnapshot((guides + otherExact).toSet(), emptySet())
        val canonical = m.canonicalPackets(offered)
        assertEquals(expected, storageCoordinates(canonical))
        assertEquals(expected, storageCoordinates(canonical.flatMap(m::canonicalPackets)), "Idempotent packet")
        val group = TaintGroup(m, m.newInterners().taint)
        assertEquals(expected, storageCoordinates(group.addAll(offered)))
        assertEquals(expected, storageCoordinates(group.all().toList()))
        assertTrue(group.addAll(offered).isEmpty())
    }

    @Test fun `concrete demand ANY root and children are fresh in both arrival orders`() = with(v) {
        val heads = listOf(p(), p(f), p(f, g))
        for (order in listOf(heads, heads.reversed())) {
            val group = TaintGroup(m, m.newInterners().taint)
            val expected = LinkedHashSet<Conclusion>()
            for (path in order) {
                val atom = leaf(path, Tail.ANY, layer = Layer.DEMAND)
                val offered = pack(atom) as TaintTree
                assertEquals(StorageCoordinateSnapshot(setOf(atom), emptySet()),
                    storageCoordinates(group.addAll(offered)), "Fresh $path in $order")
                expected += atom
                assertEquals(StorageCoordinateSnapshot(expected.toSet(), emptySet()),
                    storageCoordinates(group.all().toList()))
                assertTrue(group.addAll(offered).isEmpty(), "Literal duplicate is not fresh")
            }
        }
    }

    @Test fun `NORMAL MUST keeps old data coverage separate from DEMAND MAY`() = with(v) {
        val group = TaintGroup(m, m.newInterners().taint)
        val normalRoot = leaf(p(), Tail.ANY_TAINT)
        group.addAll(rawStoragePacket(normalRoot))
        assertTrue(group.addAll(rawStoragePacket(leaf(p(f), Tail.ANY_TAINT))).isEmpty())
        val demand = listOf(leaf(p(), Tail.ANY, layer = Layer.DEMAND),
            leaf(p(f), Tail.ANY, layer = Layer.DEMAND))
        for (atom in demand) group.addAll(pack(atom) as TaintTree)
        assertEquals(StorageCoordinateSnapshot((demand + normalRoot).toSet(), emptySet()),
            storageCoordinates(group.all().toList()))
    }

    @Test fun `actual ZERO point owner keeps the fine child and its fresh delta`() = with(v) {
        val s = AccessPathBase.LocalVar(0)
        val root = leaf(p(), Tail.ANY, layer = Layer.DEMAND, base = s)
        val child = leaf(p(f), Tail.ANY, layer = Layer.DEMAND, base = s)
        val store = MethodEdgeStore(m, fixture.method, fixture.lm, 3)
        val point = fixture.inst(5)
        store.addAll(point, m.zero, pack(root))
        assertEquals(StorageCoordinateSnapshot(setOf(child), emptySet()),
            storageCoordinates(store.addAll(point, m.zero, pack(child))))
        assertEquals(mapOf<PremiseKey, StorageCoordinateSnapshot>(m.zero to StorageCoordinateSnapshot(setOf(root, child), emptySet())),
            storageCoordinateRows(store.edgesAt(point)))
        assertTrue(store.addAll(point, m.zero, pack(child)).isEmpty())
        assertTrue(store.edgesAt(fixture.inst(6)).none(), "Producing point owns the row")
        assertTrue(store.edgesAt(point, premise()).none(), "Original P stays ZERO")
    }

    @Test fun `scoped ZERO summary hands off both coordinates with their real ports`() = with(v) {
        val s = AccessPathBase.LocalVar(0)
        val root = leaf(p(), Tail.ANY, layer = Layer.DEMAND, base = s)
        val child = leaf(p(f), Tail.ANY, layer = Layer.DEMAND, base = s)
        val scope = BlockScope(BlockId(3), PortId.ROOT_ENTRY)
        val exit = PortId(7)
        val stores = PortSummaryStores(m)
        val rows = stores.at(exit)
        rows.addAdmittedAll(m.zero, pack(root))
        rows.addAdmittedAll(m.zero, pack(child))
        assertEquals(mapOf<PremiseKey, StorageCoordinateSnapshot>(m.zero to StorageCoordinateSnapshot(setOf(root, child), emptySet())),
            storageCoordinateRows(rows.all()))
        assertNull(stores.existing(PortId(8)), "An unentered exit has no summary")
        val key = ScopedSummaryKey(fixture.method, scope, exit)
        val observed = LinkedHashSet<Triple<ScopedSummaryKey, Pattern, Pattern>>()
        val demand = DemandStore.Builder(m)
        val counts = LinkedHashMap<MethodKey, Int>()
        projectBlockHandOff(m, Direction.BACKWARD, false,
            sequenceOf(ScopedRunSummary(key, rows)), emptySequence(), demand, counts) { owner, from, to ->
            observed += Triple(owner, from, to)
        }
        assertEquals(setOf(root, child).map {
            Triple(key, m.zero.toPattern(), Pattern(it.fact, it.exclusion))
        }.toSet(), observed)
        assertEquals(2, counts[fixture.method])
        assertEquals(ScopedSummaryKey(fixture.method, BlockScope(BlockId(3), exit), scope.entry), key.reversed())
    }

    @Test fun `cold packed concrete guide geometry and fallback retain full mark rows`() = with(v) {
        val store = DiagonalRelations(m)
        val packet = coordinatePacket(listOf(p(), p(f)), atoms = listOf(t, u))
        val expected = storageCoordinateRows(decodeCoordinates(packet).asSequence())
        assertEquals(expected, storageCoordinateRows(admitCoordinatePacket(store, packet).asSequence()))
        assertEquals(expected, storageCoordinateRows(store.all()))
        assertTrue(admitCoordinatePacket(store, packet).isEmpty())
        val later = coordinatePacket(listOf(p(f, g)), atoms = listOf(t))
        val beforeU = storageCoordinates(store.borrow(premise(tail = Tail.STAR, mark = mu)).toList())
        val fresh = admitCoordinatePacket(store, later)
        assertEquals(storageCoordinateRows(decodeCoordinates(later).asSequence()),
            storageCoordinateRows(fresh.asSequence()))
        assertEquals(beforeU, storageCoordinates(store.borrow(premise(tail = Tail.STAR, mark = mu)).toList()))
        assertTrue(admitCoordinatePacket(store, later).isEmpty())
    }

    @Test fun `plain FLOW replacement remains selected independently of guide retention`() = with(v) {
        val key = premise(tail = Tail.STAR)
        val flowKey = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        val concrete = pack(leaf(p(f), Tail.ANY, layer = Layer.DEMAND, base = y))
        val cover = pack(leaf(p(), Tail.ANY, MarkSlot.STAR, Layer.DEMAND, base = y))
        for (flowFirst in listOf(false, true)) {
            val rows = RunSummaryStore(m, flowBacked = true)
            val input = listOf(key to concrete, flowKey to cover)
            for ((initial, value) in if (flowFirst) input.reversed() else input) rows.addAdmittedAll(initial, value)
            assertTrue(rows.borrow(key).none(), "No new exemption from complete FLOW replacement")
            assertEquals(mapOf<PremiseKey, StorageCoordinateSnapshot>(flowKey to storageCoordinates(listOf(cover))), storageCoordinateRows(rows.all()))
        }
    }
}
