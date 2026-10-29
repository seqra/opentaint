package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.InitialFactStore
import org.opentaint.dataflow.bidi.store.PathTrie
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/** Small valid queries for the workload investigation. No timing assertion or optimized algorithm. */
class DemandCandidateWorkloadTest {
    private fun patterns(ops: ApOps, values: List<Facts>): Set<Conclusion> = values.flatMap { value ->
        ops.leaves(value).map { Conclusion(it.fact, it.exclusion, value.layer == Layer.DEMAND) }.toList()
    }.toSet()

    private fun countedStore(fixture: StoreFixtures, demands: List<DemandPattern>): DemandStore {
        val property = "org.opentaint.bidi.optimizationStatistics"
        val previous = System.getProperty(property)
        return try {
            System.setProperty(property, "true")
            DemandStore.Builder(fixture.manager).apply {
                demands.forEach { assertTrue(add(fixture.method, it)) }
            }.build()
        } finally {
            if (previous == null) System.clearProperty(property) else System.setProperty(property, previous)
        }
    }

    /**
     * Code shape: Box fanout(Object p, int choice) { switch (choice) { case i: r.fi = p; } return r; }
     * Raw: p.* -> {ret.f0.*, ..., ret.fK.*}. Demand: one paired exit per field, same p.* entry.
     * The exit trie finds K useful leaf/row pairs. A full scan has K*K scalar cells and K results.
     * The production counter measures K whole-packet restrict calls, not their inner scalar cells.
     */
    @Test
    fun `disjoint paired exits retain K outputs while packet restriction repeats K candidates`() {
        for (count in listOf(1, 4, 16, 64)) checkDisjointExits(count, protected = false)
    }

    @Test
    fun `disjoint paired exits preserve protection on the same K outputs`() {
        for (count in listOf(1, 4, 16)) checkDisjointExits(count, protected = true)
    }

    private fun checkDisjointExits(count: Int, protected: Boolean) {
        val f = StoreFixtures()
        val m = f.manager
        val mark = if (protected) MarkSlot.Concrete(f.mark("T")) else MarkSlot.STAR
        val layer = if (protected) Layer.DEMAND else Layer.NORMAL
        fun at(base: AccessPathBase, path: List<Int> = emptyList()) =
            Pattern(PathFact(base, path, Tail.STAR, mark), ExclusionSet.Empty)
        val entry = at(AccessPathBase.Argument(0))
        val exits = (0 until count).map { at(AccessPathBase.Return, listOf(f.field("f$it"))) }
        val demands = exits.map { DemandPattern(entry, it) }
        val store = countedStore(f, demands)
        val initial = m.initial(entry)
        val raw = exits.map { m.factsOf(it.fact, it.exclusion, layer) }.reduce { a, b ->
            m.mergeAddDelta(a, b).first
        }.let { if (protected) (it as TaintTree).withProtection(it.root) else it }
        val leaves = f.ops.leaves(raw).toList()
        assertEquals(count, leaves.size)

        var scalarAttempts = 0
        val reference = buildSet {
            for (demand in demands) for (leaf in leaves) {
                scalarAttempts++
                restrict(entry, Conclusion(leaf.fact, leaf.exclusion, layer == Layer.DEMAND), demand, m.marks)
                    ?.let(::add)
            }
        }
        val indexedPairs = PathTrie<Int>().apply {
            exits.forEachIndexed { id, exit -> add(exit.fact.base, exit.fact.path.toIntArray(), id) }
        }
        val relevantLeafRowPairs = leaves.sumOf { leaf ->
            indexedPairs.around(leaf.fact.base, leaf.fact.path.toIntArray()).size
        }
        assertEquals(count * count, scalarAttempts)
        assertEquals(count, relevantLeafRowPairs)
        val actual = store.intersect(f.method, initial, raw)
        assertEquals(count, reference.size)
        assertEquals(reference, patterns(f.ops, actual))
        val restrictionCalls = Regex("(?:^| )c5Restrict=(\\d+)(?: |$)")
            .find(checkNotNull(store.staticCompletionStatistics()))!!.groupValues[1].toLong()
        assertEquals(count.toLong(), restrictionCalls)
        if (protected) {
            val protectedLeaves = actual.flatMap { value ->
                (value as TaintTree).protectedPart()?.let { f.ops.leaves(it).toList() }.orEmpty()
            }.toSet()
            assertEquals(leaves.toSet(), protectedLeaves)
        }
    }

    /** C2 is a pure demand query. Method admission deduplicates its repeated answer afterward. */
    @Test
    fun `different actual marks can repeatedly select one already admitted FLOW initial`() {
        val f = StoreFixtures()
        val p = AccessPathBase.Argument(0)
        val entry = f.pattern(base = p, tail = Tail.STAR, mark = MarkSlot.STAR)
        val exit = f.pattern(base = AccessPathBase.Return, tail = Tail.STAR, mark = MarkSlot.STAR)
        val store = countedStore(f, listOf(DemandPattern(entry, exit)))
        val held = InitialFactStore()
        val first = store.initials(f.method, f.fact(base = p, mark = MarkSlot.Concrete(f.mark("T")))).single()
        assertTrue(held.add(first))
        val second = store.initials(f.method, f.fact(base = p, mark = MarkSlot.Concrete(f.mark("U")))).single()
        assertEquals(f.manager.initial(entry), first)
        assertTrue(first === second)
        assertFalse(held.add(second), "The method already has this FLOW initial; the C2 query returned it again")
    }
}
