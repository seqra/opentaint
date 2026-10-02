package org.opentaint.dataflow.ap.ifds.markset

import java.util.BitSet
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * Kotlin twins of the Lean witness programs. Each builds the same program by
 * hand (method = node, as in the Lean witnesses) and checks the scan against
 * the property the Lean theorem states.
 */
class MarkSetScanTest {
    private companion object {
        const val BASE_STRIDE = 100
    }

    /** A positive literal on `(base, mark)`; distinct bases give distinct literal ids. */
    private fun lit(mark: Int, base: Int = 0): MarkCond.Lit = MarkCond.Lit(mark, base * BASE_STRIDE + mark)

    private fun site(method: Int, kind: SiteKind, cond: MarkCond, vararg gens: Int) =
        MarkSite(method, kind, cond, gens)

    private fun program(
        methodCount: Int,
        markCount: Int,
        roots: List<Int>,
        calls: Map<Int, List<Int>>,
        sites: List<MarkSite>,
        cleanerAtoms: BitSet = BitSet(),
    ) = MarkSetProgram(
        methodCount = methodCount,
        markCount = markCount,
        roots = roots.toIntArray(),
        callees = Array(methodCount) { (calls[it] ?: emptyList()).distinct().toIntArray() },
        sites = sites,
        cleanerAtoms = cleanerAtoms,
    )

    private fun BitSet.toSet(): Set<Int> = stream().toArray().toSet()

    // ---- D1: joined cubes are evaluated on the method-level union ------------

    @Test
    fun `d1_applicable - a joined sink over two roots is applicable though no root holds both marks`() {
        val markA = 1
        val markB = 2
        val sink = site(3, SiteKind.SINK, MarkCond.And(listOf(lit(markA, base = 0), lit(markB, base = 1))))
        val p = program(
            methodCount = 4, markCount = 3,
            roots = listOf(1, 2),
            calls = mapOf(1 to listOf(3), 2 to listOf(3)),
            sites = listOf(
                site(1, SiteKind.SOURCE, MarkCond.True, markA),
                site(2, SiteKind.SOURCE, MarkCond.True, markB),
                sink,
            ),
        )

        val result = MarkSetScan.run(p)

        assertTrue(result.applicable.get(2), "the D1 sink must be applicable")
        for (root in listOf(1, 2)) {
            val marks = result.rootMarks.getValue(root)
            assertFalse(marks.get(markA) && marks.get(markB), "root $root must not hold both marks: $marks")
        }
        assertEquals(setOf(markA), result.rootMarks.getValue(1).toSet())
        assertEquals(setOf(markB), result.rootMarks.getValue(2).toSet())
        assertEquals(setOf(markA, markB), result.needed.toSet())
    }

    // ---- D4: relevance must close backward over transformers -----------------

    @Test
    fun `backward_closure_necessary - the transformer input mark is needed`() {
        val p = program(
            methodCount = 1, markCount = 3,
            roots = listOf(0),
            calls = emptyMap(),
            sites = listOf(
                site(0, SiteKind.SOURCE, MarkCond.True, 1),
                site(0, SiteKind.SOURCE, lit(1), 2),
                site(0, SiteKind.SINK, lit(2)),
            ),
        )

        val result = MarkSetScan.run(p)

        assertEquals(setOf(0, 1, 2), result.applicable.toSet())
        assertEquals(setOf(1, 2), result.needed.toSet())
    }

    // ---- G1: sink gens are zero-context facts ---------------------------------

    @Test
    fun `sinkgen_zero_ctx_needed - an end mark from a sink under root 1 enables a sink in root 2`() {
        val markA = 1
        val markT = 2
        val sinkT = site(2, SiteKind.SINK, lit(markT))
        val p = program(
            methodCount = 4, markCount = 3,
            roots = listOf(1, 2),
            calls = mapOf(1 to listOf(3), 2 to listOf(3)),
            sites = listOf(
                site(1, SiteKind.SOURCE, MarkCond.True, markA),
                site(3, SiteKind.SINK, lit(markA), markT),
                sinkT,
            ),
        )

        val result = MarkSetScan.run(p)

        assertTrue(result.rootMarks.getValue(2).get(markT), "T must reach root 2 through the zero context")
        assertEquals(setOf(0, 1, 2), result.applicable.toSet())
    }

    // ---- G3: the joined placement reaches every caller -------------------------

    private fun g3Program(): MarkSetProgram = program(
        methodCount = 5, markCount = 4,
        roots = listOf(1, 2, 3),
        calls = mapOf(1 to listOf(4), 2 to listOf(4), 3 to listOf(4)),
        sites = listOf(
            site(1, SiteKind.SOURCE, MarkCond.True, 1),
            site(2, SiteKind.SOURCE, MarkCond.True, 2),
            site(4, SiteKind.SOURCE, MarkCond.And(listOf(lit(1, base = 0), lit(2, base = 1))), 3),
            site(3, SiteKind.SINK, lit(3, base = 5)),
        ),
    )

    @Test
    fun `naive_relax_unsound - the E3 sink is applicable in exact mode`() {
        val result = MarkSetScan.run(g3Program())

        assertTrue(result.rootMarks.getValue(3).get(3), "C must land in S_E3")
        assertTrue(result.applicable.get(3), "the E3 sink on C must be applicable")
        assertEquals(setOf(1, 2, 3), result.needed.toSet())
    }

    @Test
    fun `naive_relax_unsound - the E3 sink is applicable with option 4-star`() {
        val result = MarkSetScan.run(g3Program(), MarkSetOptions(relaxed = true))

        assertTrue(result.rootMarks.getValue(3).get(3), "C must land in S_E3")
        assertTrue(result.applicable.get(3), "the E3 sink on C must be applicable")
    }

    @Test
    fun `option 4-star fires a joined cube on one mark`() {
        // Only A is ever present; the exact joined test fails, the relaxed one holds.
        val p = program(
            methodCount = 2, markCount = 4,
            roots = listOf(0),
            calls = mapOf(0 to listOf(1)),
            sites = listOf(
                site(0, SiteKind.SOURCE, MarkCond.True, 1),
                site(1, SiteKind.SOURCE, MarkCond.And(listOf(lit(1, base = 0), lit(2, base = 1))), 3),
                site(0, SiteKind.SINK, lit(3)),
            ),
        )

        val exact = MarkSetScan.run(p)
        assertEquals(setOf(0), exact.applicable.toSet())

        val relaxed = MarkSetScan.run(p, MarkSetOptions(relaxed = true))
        assertEquals(setOf(0, 1, 2), relaxed.applicable.toSet())
        assertTrue(relaxed.rootMarks.getValue(0).get(3))
    }

    // ---- recursion and reachability ----------------------------------------

    @Test
    fun `a source in a recursive callee reaches a sink in its caller`() {
        // root 0 -> A = 1 <-> B = 2; source in B, sink in A.
        val p = program(
            methodCount = 3, markCount = 2,
            roots = listOf(0),
            calls = mapOf(0 to listOf(1), 1 to listOf(2), 2 to listOf(1)),
            sites = listOf(
                site(2, SiteKind.SOURCE, MarkCond.True, 1),
                site(1, SiteKind.SINK, lit(1)),
            ),
        )

        val result = MarkSetScan.run(p)

        assertEquals(setOf(1), result.rootMarks.getValue(0).toSet())
        assertEquals(setOf(0, 1), result.applicable.toSet())
        assertEquals(setOf(1), result.needed.toSet())
    }

    @Test
    fun `sites of an unreachable method are never applicable`() {
        val p = program(
            methodCount = 2, markCount = 3,
            roots = listOf(0),
            calls = emptyMap(),
            sites = listOf(
                site(0, SiteKind.SOURCE, MarkCond.True, 1),
                site(1, SiteKind.SOURCE, MarkCond.True, 2),
                site(1, SiteKind.SINK, MarkCond.True),
                site(1, SiteKind.SINK, lit(1)),
            ),
        )

        val result = MarkSetScan.run(p)

        assertEquals(setOf(0), result.applicable.toSet())
        assertEquals(setOf(1), result.rootMarks.getValue(0).toSet())
        assertEquals(emptySet(), result.needed.toSet())
        assertEquals(0, result.stats.applicableSinks)
    }

    @Test
    fun `cleaner atoms are always needed`() {
        val p = program(
            methodCount = 1, markCount = 3,
            roots = listOf(0),
            calls = emptyMap(),
            sites = listOf(site(0, SiteKind.SOURCE, MarkCond.True, 1)),
            cleanerAtoms = BitSet().apply { set(2) },
        )

        assertEquals(setOf(2), MarkSetScan.run(p).needed.toSet())
    }

    // ---- cost ------------------------------------------------------------------

    @Test
    fun `fam_speedup - a thousand sites sharing one signature under fifty roots`() {
        val siteCount = 1000
        val rootCount = 50
        val p = program(
            methodCount = rootCount + 1, markCount = 2,
            roots = (1..rootCount).toList(),
            calls = (1..rootCount).associateWith { listOf(0) },
            sites = List(siteCount) { site(0, SiteKind.SOURCE, MarkCond.True, 1) },
        )

        val start = System.nanoTime()
        val result = MarkSetScan.run(p)
        val elapsedMs = (System.nanoTime() - start) / 1_000_000

        assertEquals(1, result.stats.signatures)
        assertEquals(1, result.stats.distinctRootSets)
        assertEquals(siteCount, result.applicable.cardinality())
        assertTrue(elapsedMs < 1000, "took $elapsedMs ms")
    }

    // ---- Scc ---------------------------------------------------------------------

    @Test
    fun `condense lists callees before callers and marks unreachable methods`() {
        // 0 -> 1 <-> 2 -> 3; 4 is unreachable.
        val succ = arrayOf(intArrayOf(1), intArrayOf(2), intArrayOf(1, 3), intArrayOf(), intArrayOf(0))
        val c = Scc.condense(5, succ, intArrayOf(0))

        assertEquals(-1, c.compOf[4])
        assertEquals(c.compOf[1], c.compOf[2])
        assertEquals(3, c.comps.size)
        for (comp in c.comps.indices) {
            for (s in c.compSucc[comp]) {
                assertTrue(s < comp, "successor component $s must come before $comp")
            }
        }
        assertTrue(c.compSucc[c.compOf[1]].contentEquals(intArrayOf(c.compOf[3])))
    }
}
