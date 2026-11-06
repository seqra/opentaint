package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** Supplied protected scalar coordinates survive coverage, not semantic transfers. */
class ProtectedStorageCoordinatesTest {
    private val fixture = StoreFixtures()
    private val v = StoreValues(fixture)

    private fun protected(vararg atoms: Conclusion): TaintTree = with(v) {
        rawStoragePacket(*atoms).let { it.withProtection(it.root) }
    }

    @Test fun `protected root and child survive cold and both orders for every tail and layer`() = with(v) {
        for (layer in Layer.entries) for (tail in listOf(Tail.EXACT, Tail.ANY, Tail.STAR, Tail.ANY_TAINT)) {
            if (tail == Tail.ANY && layer == Layer.NORMAL) continue // W6
            val atoms = listOf(leaf(p(), tail, layer = layer), leaf(p(f), tail, layer = layer))
            for (offers in listOf(listOf(protected(*atoms.toTypedArray())),
                atoms.map { protected(it) }, atoms.reversed().map { protected(it) })) {
                val group = TaintGroup(m, m.newInterners().taint)
                for (offer in offers) group.addAll(offer)
                val expected = StorageCoordinateSnapshot(atoms.toSet(), atoms.toSet())
                assertEquals(expected, storageCoordinates(group.all().toList()), "$layer/$tail/$offers")
                for (offer in offers) assertTrue(group.addAll(offer).isEmpty(), "Protected duplicate")
            }
        }
    }

    @Test fun `protected MAY never absorbs protected EXACT at or below the same point`() = with(v) {
        for (layer in listOf(Layer.DEMAND)) for (path in listOf(p(), p(f, g))) {
            val any = leaf(p(), Tail.ANY, layer = layer)
            val exact = leaf(path, Tail.EXACT, layer = layer)
            for (offers in listOf(listOf(protected(any, exact)),
                listOf(protected(any), protected(exact)), listOf(protected(exact), protected(any)))) {
                val group = TaintGroup(m, m.newInterners().taint)
                for (offer in offers) group.addAll(offer)
                assertEquals(StorageCoordinateSnapshot(setOf(any, exact), setOf(any, exact)),
                    storageCoordinates(group.all().toList()))
                for (offer in offers) assertTrue(group.addAll(offer).isEmpty())
            }
        }
    }

    @Test fun `protected STAR and MUST keep both original exclusion headers alongside plain join`() = with(v) {
        for (layer in Layer.entries) for (tail in listOf(Tail.STAR, Tail.ANY_TAINT)) {
            val ef = leaf(p(), tail, layer = layer, e = ex(f))
            val eg = leaf(p(), tail, layer = layer, e = ex(g))
            val joined = leaf(p(), tail, layer = layer)
            for (order in listOf(listOf(ef, eg), listOf(eg, ef))) {
                val group = TaintGroup(m, m.newInterners().taint)
                for (atom in order) group.addAll(protected(atom))
                assertEquals(StorageCoordinateSnapshot(setOf(ef, eg, joined), setOf(ef, eg)),
                    storageCoordinates(group.all().toList()), "$layer/$tail/$order")
                for (atom in order) assertTrue(group.addAll(protected(atom)).isEmpty())
            }
        }
    }

    @Test fun `whole-root STAR join retains plain Empty E and the original one-sided protected E`() = with(v) {
        for (layer in Layer.entries) {
            val ef = leaf(p(), Tail.STAR, layer = layer, e = ex(f))
            val eg = leaf(p(), Tail.STAR, layer = layer, e = ex(g))
            val joined = leaf(p(), Tail.STAR, layer = layer)
            for (protectedFirst in listOf(false, true)) {
                val group = TaintGroup(m, m.newInterners().taint)
                val offers = listOf(protected(ef), pack(eg) as TaintTree)
                for (offer in if (protectedFirst) offers else offers.reversed()) group.addAll(offer)
                assertEquals(StorageCoordinateSnapshot(setOf(joined, ef), setOf(ef)),
                    storageCoordinates(group.all().toList()))
                assertTrue(group.addAll(protected(ef)).isEmpty())
                assertTrue(group.addAll(pack(eg) as TaintTree).isEmpty())
            }
        }
    }

    @Test fun `MUST hole fill does not replace the original protected excluded header`() = with(v) {
        for (layer in Layer.entries) {
            val old = leaf(p(), Tail.ANY_TAINT, layer = layer, e = ex(f))
            val fill = leaf(p(f), Tail.ANY_TAINT, layer = layer)
            val complete = leaf(p(), Tail.ANY_TAINT, layer = layer)
            val group = TaintGroup(m, m.newInterners().taint)
            group.addAll(protected(old))
            group.addAll(pack(fill) as TaintTree)
            val actual = storageCoordinates(group.all().toList())
            assertEquals(setOf(old), actual.flags)
            assertTrue(actual.ordinary.containsAll(setOf(old, complete)), "Keep old DATA fill and raw protected E")
            assertTrue(group.addAll(protected(old)).isEmpty())
        }
    }

    @Test fun `protected EXACT ignores its mixed wrapper tail and E when deduplicating`() = with(v) {
        for (layer in Layer.entries) {
            val exact = leaf(p(g), Tail.EXACT, layer = layer)
            val first = pack(leaf(p(), Tail.STAR, mu, layer, ex(f)), exact) as TaintTree
            val second = pack(leaf(p(), Tail.ANY_TAINT, mu, layer, ex(h)), exact) as TaintTree
            val mask = (pack(exact) as TaintTree).root
            val group = TaintGroup(m, m.newInterners().taint)
            group.addAll(first.withProtection(mask))
            val delta = group.addAll(second.withProtection(mask))
            assertEquals(setOf(exact), storageCoordinates(group.all().toList()).flags)
            assertTrue(storageCoordinates(delta).flags.isEmpty(), "No second protected exact atom from a new wrapper")
            assertTrue(group.addAll(second.withProtection(mask)).isEmpty())
        }
    }

    /** The scalar reference has an independent explicit protected-key oracle. */
    private fun packedParity(offers: List<TaintTree>, packets: Boolean) = with(v) {
        val scalar = TaintGroup(m, m.newInterners().taint)
        val packed = DiagonalRelations(m)
        val key = premise(tail = Tail.STAR)
        val expectedFlags = LinkedHashSet<Conclusion>()
        for ((step, offered) in offers.withIndex()) {
            expectedFlags += storageCoordinates(listOf(offered)).flags
            val expectedFresh = scalar.addAll(offered)
            val fresh = if (packets && (offered.nonSubsumable == null || offered.nonSubsumable == offered.root)) {
                val packet = coordinatePacket(fixture.ops.leaves(offered).map { it.fact.path }.toList(),
                    offered.nonSubsumable != null, tail = offered.anyTail, layer = offered.layer, e = offered.exclusion)
                admitCoordinatePacket(packed, packet).map { it.second }
            } else packed.addAll(key, offered)
            assertEquals(storageCoordinates(expectedFresh), storageCoordinates(fresh), "Fresh step $step")
            val actual = storageCoordinates(packed.borrow(key).toList())
            assertEquals(storageCoordinates(scalar.all().toList()), actual, "Current step $step")
            assertEquals(expectedFlags.toSet(), actual.flags, "No lost or invented protected coordinate")
            assertTrue(actual.ordinary.containsAll(expectedFlags))
            assertTrue(packed.addAll(key, offered).isEmpty(), "Duplicate step $step")
        }
    }

    @Test fun `packed admission keeps protected root child and typed E coordinates in both layers`() = with(v) {
        for (layer in Layer.entries) for (packets in listOf(false, true)) {
            // NORMAL/ANY is only a raw TaintGroup cell above. Packed native
            // NORMAL uses STAR; ANY uses its existing DEMAND scalar grammar.
            val tails = if (layer == Layer.NORMAL) listOf(Tail.STAR) else listOf(Tail.ANY, Tail.STAR)
            for (tail in tails) {
                val root = protected(leaf(p(), tail, layer = layer, base = y))
                val child = protected(leaf(p(f), tail, layer = layer, base = y))
                packedParity(listOf(protected(leaf(p(), tail, layer = layer, base = y),
                    leaf(p(f), tail, layer = layer, base = y))), packets)
                packedParity(listOf(root, child), packets)
                packedParity(listOf(child, root), packets)
            }
            val ef = protected(leaf(p(), Tail.STAR, layer = layer, e = ex(f), base = y))
            val eg = protected(leaf(p(), Tail.STAR, layer = layer, e = ex(g), base = y))
            packedParity(listOf(ef, eg), packets)
            packedParity(listOf(eg, ef), packets)
        }
    }

    @Test fun `packed plain ancestors and protected descendants never infer flags in either order`() = with(v) {
        val root = leaf(p(), Tail.ANY, layer = Layer.DEMAND, base = y)
        val child = leaf(p(f), Tail.ANY, layer = Layer.DEMAND, base = y)
        for (packets in listOf(false, true)) for (protectedRoot in listOf(false, true)) {
            val a = if (protectedRoot) protected(root) else pack(root) as TaintTree
            val b = if (protectedRoot) pack(child) as TaintTree else protected(child)
            packedParity(listOf(a, b), packets)
            packedParity(listOf(b, a), packets)
        }
    }

    @Test fun `shared packed mark geometry preserves the other atom and never spreads protection`() = with(v) {
        val rootT = leaf(p(), Tail.ANY, layer = Layer.DEMAND, base = y)
        val childT = leaf(p(f), Tail.ANY, layer = Layer.DEMAND, base = y)
        val rootU = rootT.copy(fact = rootT.fact.copy(mark = mu))
        for (childFirst in listOf(false, true)) {
            val store = DiagonalRelations(m)
            val root = coordinatePacket(listOf(p()), atoms = listOf(t, u))
            val child = coordinatePacket(listOf(p(f)), protected = true)
            for (packet in if (childFirst) listOf(child, root) else listOf(root, child))
                admitCoordinatePacket(store, packet)
            val expected = mapOf<PremiseKey, StorageCoordinateSnapshot>(
                premise(tail = Tail.STAR) to StorageCoordinateSnapshot(setOf(rootT, childT), setOf(childT)),
                premise(tail = Tail.STAR, mark = mu) to StorageCoordinateSnapshot(setOf(rootU), emptySet()))
            assertEquals(expected, storageCoordinateRows(store.all()))
            assertTrue(admitCoordinatePacket(store, child).isEmpty())
            assertTrue(admitCoordinatePacket(store, root).isEmpty())
        }
    }

    @Test fun `mixed full marks and partial flags survive diagonal scalar fallback recombination`() = with(v) {
        val atoms = listOf(leaf(p(), Tail.ANY, layer = Layer.DEMAND, base = y),
            leaf(p(f), Tail.ANY, layer = Layer.DEMAND, base = y),
            leaf(p(), Tail.ANY, mu, Layer.DEMAND, base = y),
            leaf(p(f), Tail.ANY, mu, Layer.DEMAND, base = y))
        val mixed = pack(*atoms.toTypedArray()) as TaintTree
        val childT = (pack(atoms[1]) as TaintTree).root
        for (flowBacked in listOf(false, true)) {
            val store = RunSummaryStore(m, flowBacked)
            val key = premise(tail = Tail.STAR)
            store.addAdmittedAll(key, mixed.withProtection(childT))
            assertEquals(StorageCoordinateSnapshot(atoms.toSet(), setOf(atoms[1])),
                storageCoordinates(store.borrow(key).toList()))
            val late = protected(atoms[2])
            val fresh = store.addAdmittedAll(key, late)
            assertEquals(setOf(atoms[2]), storageCoordinates(fresh).flags)
            assertEquals(StorageCoordinateSnapshot(atoms.toSet(), setOf(atoms[1], atoms[2])),
                storageCoordinates(store.borrow(key).toList()))
            assertTrue(store.addAdmittedAll(key, late).isEmpty())
        }
    }

    @Test fun `FLOW compaction preserves protected rows in scalar and packed summary owners`() = with(v) {
        val key = premise(tail = Tail.STAR)
        val flowKey = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        val protectedChild = protected(leaf(p(f), Tail.ANY, layer = Layer.DEMAND, base = y))
        val flow = pack(leaf(p(), Tail.ANY, MarkSlot.STAR, Layer.DEMAND, base = y))
        for (flowFirst in listOf(false, true)) {
            val store = RunSummaryStore(m, flowBacked = true)
            val offers = listOf(key to protectedChild, flowKey to flow)
            for ((initial, facts) in if (flowFirst) offers.reversed() else offers) store.addAdmittedAll(initial, facts)
            assertEquals(storageCoordinates(listOf(protectedChild)), storageCoordinates(store.borrow(key).toList()))
            assertTrue(store.addAdmittedAll(key, protectedChild).isEmpty())
        }
    }

    @Test fun `eligible NORMAL records retain protected original E headers and scoped ownership`() = with(v) {
        val key = premise()
        val scope = BlockScope(BlockId(3), PortId.ROOT_ENTRY)
        val exit = PortId(7)
        val ef = leaf(p(), Tail.STAR, e = ex(f), base = y)
        val eg = leaf(p(), Tail.STAR, e = ex(g), base = y)
        val joined = leaf(p(), Tail.STAR, base = y)
        val summary = RunSummaryStore(m)
        summary.addAdmittedAll(key, protected(ef))
        summary.addAdmittedAll(key, protected(eg))
        val records = PersistentRecordStore(m)
        records.persistScoped(Direction.FORWARD, sequenceOf(
            ScopedRunSummary(ScopedSummaryKey(fixture.method, scope, exit), summary)))
        val rows = records.byEntry(fixture.method, scope, key.toPattern()).toList()
        assertEquals(StorageCoordinateSnapshot(setOf(ef, eg, joined), setOf(ef, eg)),
            storageCoordinates(rows.map { it.conclusion }))
        assertTrue(rows.all { it.scope == scope && it.exit == exit && it.premise === key })
        assertTrue(records.byEntry(fixture.method, key.toPattern()).none(), "Scoped rows stay local")
        assertTrue(records.byEntry(fixture.method, BlockScope(BlockId(3), PortId(8)), key.toPattern()).none())
    }
}
