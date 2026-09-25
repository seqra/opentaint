package org.opentaint.dataflow.ap.ifds.markset

import java.util.BitSet
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * Kotlin twins of the Lean witness programs of `MarkScan/FlowSensitive.lean` (option 3*, spec §9).
 * Each builds the same program by hand (method = node) with an explicit statement graph.
 */
class FlowSensitiveScanTest {
    private companion object {
        const val BASE_STRIDE = 100
        const val MARK = 1
    }

    private fun lit(mark: Int, base: Int = 0): MarkCond.Lit = MarkCond.Lit(mark, base * BASE_STRIDE + mark)

    /** A site of [kind] at statement [stmt] of [method]. */
    private class At(val method: Int, val stmt: Int, val kind: SiteKind, val cond: MarkCond, val gens: IntArray)

    private fun at(method: Int, stmt: Int, kind: SiteKind, cond: MarkCond, vararg gens: Int) =
        At(method, stmt, kind, cond, gens)

    /**
     * A program whose method `m` has statements `0 until stmtCounts[m]`, entry `0`, and the given
     * successors (straight-line `s -> s + 1` where [succ] has no entry for the method) and exits
     * (the last statement where [exits] has no entry). [calls] are `(caller, stmt, callee)`.
     */
    private fun program(
        stmtCounts: IntArray,
        markCount: Int,
        roots: List<Int>,
        sites: List<At>,
        calls: List<Triple<Int, Int, Int>> = emptyList(),
        succ: Map<Int, Map<Int, List<Int>>> = emptyMap(),
        exits: Map<Int, List<Int>> = emptyMap(),
        cleanerAtoms: BitSet = BitSet(),
    ): MarkSetProgram {
        val methodCount = stmtCounts.size
        val callsAt = Array(methodCount) { m -> Array(stmtCounts[m]) { IntArray(0) } }
        val callees = Array(methodCount) { LinkedHashSet<Int>() }
        for ((caller, stmt, callee) in calls) {
            callsAt[caller][stmt] = callsAt[caller][stmt] + callee
            callees[caller] += callee
        }
        val cfg = MethodCfg(
            stmtCount = stmtCounts,
            succ = Array(methodCount) { m ->
                Array(stmtCounts[m]) { s ->
                    succ[m]?.let { (it[s] ?: emptyList()).toIntArray() }
                        ?: if (s + 1 < stmtCounts[m]) intArrayOf(s + 1) else IntArray(0)
                }
            },
            entry = IntArray(methodCount),
            exits = Array(methodCount) { m -> (exits[m] ?: listOf(stmtCounts[m] - 1)).toIntArray() },
            siteStmt = sites.map { it.stmt }.toIntArray(),
            callsAt = callsAt,
        )
        return MarkSetProgram(
            methodCount = methodCount,
            markCount = markCount,
            roots = roots.toIntArray(),
            callees = Array(methodCount) { callees[it].toIntArray() },
            sites = sites.map { MarkSite(it.method, it.kind, it.cond, it.gens) },
            cleanerAtoms = cleanerAtoms,
            cfg = cfg,
        )
    }

    private fun BitSet.toSet(): Set<Int> = stream().toArray().toSet()

    private fun fs(p: MarkSetProgram, options: MarkSetOptions = MarkSetOptions()) =
        FlowSensitiveScan.run(p, options) {}

    // ---- fs_strict ----------------------------------------------------------

    @Test
    fun `fs_strict - a sink before a source in one method is FI-applicable but not FS-applicable`() {
        // Lean `exOrder`: pc 0 is the sink, pc 1 the source, edge 0 -> 1, no loop.
        val p = program(
            stmtCounts = intArrayOf(2), markCount = 2, roots = listOf(0),
            sites = listOf(
                at(0, 0, SiteKind.SINK, lit(MARK)),
                at(0, 1, SiteKind.SOURCE, MarkCond.True, MARK),
            ),
        )

        assertTrue(MarkSetScan.run(p).applicable.get(0), "the default mode must select the sink")
        val result = fs(p)
        assertFalse(result.applicable.get(0), "option 3* must not select the sink")
        assertTrue(result.applicable.get(1), "the source is applicable")
        assertEquals(emptySet(), result.needed.toSet())
    }

    // ---- linear_order_unsound -----------------------------------------------

    @Test
    fun `linear_order_unsound - a back edge carries a later source to an earlier sink`() {
        // Lean `exLoop`: 0 -> 1 -> 2 -> 1, the sink at pc 1, the source at pc 2.
        val p = program(
            stmtCounts = intArrayOf(3), markCount = 2, roots = listOf(0),
            sites = listOf(
                at(0, 1, SiteKind.SINK, lit(MARK)),
                at(0, 2, SiteKind.SOURCE, MarkCond.True, MARK),
            ),
            succ = mapOf(0 to mapOf(0 to listOf(1), 1 to listOf(2), 2 to listOf(1))),
            exits = mapOf(0 to listOf(2)),
        )

        val result = fs(p)
        assertTrue(result.applicable.get(0), "option 3* must select the sink reached over the back edge")
        assertEquals(setOf(MARK), result.needed.toSet())
    }

    // ---- fs_ctx_needed ------------------------------------------------------

    @Test
    fun `fs_ctx_needed - a callee fact passed by one root is not in another root's set`() {
        // Lean `exCtx`: roots 0 and 1 call node 2 at pc 1; root 0 has a source at pc 0.
        // A sink at pc 1 of node 2 on the mark; a sink in root 1 after its call.
        val p = program(
            stmtCounts = intArrayOf(2, 3, 2), markCount = 2, roots = listOf(0, 1),
            sites = listOf(
                at(0, 0, SiteKind.SOURCE, MarkCond.True, MARK),
                at(2, 1, SiteKind.SINK, lit(MARK)),
                at(1, 2, SiteKind.SINK, lit(MARK)),
            ),
            calls = listOf(Triple(0, 1, 2), Triple(1, 1, 2)),
        )

        val result = fs(p)
        assertTrue(result.applicable.get(1), "the callee sink sees root 0's mark")
        assertFalse(result.applicable.get(2), "root 1 never holds the mark")
        assertEquals(setOf(MARK), result.rootMarks.getValue(0).toSet())
        assertEquals(emptySet(), result.rootMarks.getValue(1).toSet())
    }

    // ---- ret: a callee's exit set flows back to the call's successors --------

    @Test
    fun `a callee source reaches a sink after the call but not one before it`() {
        val p = program(
            stmtCounts = intArrayOf(4, 2), markCount = 2, roots = listOf(0),
            sites = listOf(
                at(0, 0, SiteKind.SINK, lit(MARK)),
                at(1, 0, SiteKind.SOURCE, MarkCond.True, MARK),
                at(0, 2, SiteKind.SINK, lit(MARK)),
            ),
            calls = listOf(Triple(0, 1, 1)),
        )

        val result = fs(p)
        assertFalse(result.applicable.get(0), "the sink before the call")
        assertTrue(result.applicable.get(2), "the sink after the call")
    }

    // ---- D1: joined cubes on the method-level union at the statement ---------

    @Test
    fun `d1 - a joined sink over two roots is applicable though no root holds both marks`() {
        val markA = 1
        val markB = 2
        val p = program(
            stmtCounts = intArrayOf(1, 2, 2, 2), markCount = 3, roots = listOf(1, 2),
            sites = listOf(
                at(1, 0, SiteKind.SOURCE, MarkCond.True, markA),
                at(2, 0, SiteKind.SOURCE, MarkCond.True, markB),
                at(3, 0, SiteKind.SINK, MarkCond.And(listOf(lit(markA, base = 0), lit(markB, base = 1)))),
            ),
            calls = listOf(Triple(1, 1, 3), Triple(2, 1, 3)),
        )

        val result = fs(p)
        assertTrue(result.applicable.get(2), "the D1 sink must be applicable")
        assertEquals(setOf(markA), result.rootMarks.getValue(1).toSet())
        assertEquals(setOf(markB), result.rootMarks.getValue(2).toSet())
        assertEquals(setOf(markA, markB), result.needed.toSet())
    }

    // ---- G1: a sink's gens go to every root reaching the sink ----------------

    @Test
    fun `sinkGen - a sink's end mark reaches a second root that never holds the sink's mark`() {
        val markA = 1
        val checked = 2
        // Root 0: source A, call 2. Root 1: call 2, then a sink on `checked`.
        // Node 2: a sink on A with end mark `checked`.
        val p = program(
            stmtCounts = intArrayOf(3, 3, 2), markCount = 3, roots = listOf(0, 1),
            sites = listOf(
                at(0, 0, SiteKind.SOURCE, MarkCond.True, markA),
                at(2, 0, SiteKind.SINK, lit(markA), checked),
                at(1, 2, SiteKind.SINK, lit(checked)),
            ),
            calls = listOf(Triple(0, 1, 2), Triple(1, 1, 2)),
        )

        val result = fs(p)
        assertTrue(result.applicable.get(2), "the second root's sink on the end mark")
        assertEquals(setOf(checked), result.rootMarks.getValue(1).toSet())
        assertEquals(setOf(markA, checked), result.needed.toSet())
    }

    @Test
    fun `sinkGen - the end mark is placed at the sink, not before it`() {
        val markA = 1
        val checked = 2
        // One root: sink on `checked` at pc 1, the source at pc 2, the sink on A with end mark at pc 3.
        val p = program(
            stmtCounts = intArrayOf(5), markCount = 3, roots = listOf(0),
            sites = listOf(
                at(0, 1, SiteKind.SINK, lit(checked)),
                at(0, 2, SiteKind.SOURCE, MarkCond.True, markA),
                at(0, 3, SiteKind.SINK, lit(markA), checked),
                at(0, 4, SiteKind.SINK, lit(checked)),
            ),
        )

        val result = fs(p)
        assertFalse(result.applicable.get(0))
        assertTrue(result.applicable.get(2))
        assertTrue(result.applicable.get(3))
    }

    // ---- the size guard -----------------------------------------------------

    @Test
    fun `the size counts the statements of the methods each root reaches`() {
        // Root 0 reaches 0, 1, 2 (2 + 3 + 4); root 1 reaches 1, 2 (3 + 4); method 3 is unreached.
        val p = program(
            stmtCounts = intArrayOf(2, 3, 4, 5), markCount = 1, roots = listOf(0, 1),
            sites = emptyList(),
            calls = listOf(Triple(0, 0, 1), Triple(1, 0, 2), Triple(2, 0, 1)),
        )
        assertEquals(9L + 7L, FlowSensitiveScan.rootPoints(p, limit = Long.MAX_VALUE))
        assertTrue(FlowSensitiveScan.rootPoints(p, limit = 10) > 10, "the count stops past the limit")
    }

    // ---- refinement on the hand-built programs --------------------------------

    @Test
    fun `option 4-star under 3-star over-approximates the exact 3-star selection`() {
        val markA = 1
        val markB = 2
        val p = program(
            stmtCounts = intArrayOf(3), markCount = 3, roots = listOf(0),
            sites = listOf(
                at(0, 0, SiteKind.SOURCE, MarkCond.True, markA),
                at(0, 1, SiteKind.SINK, MarkCond.And(listOf(lit(markA, base = 0), lit(markB, base = 1)))),
            ),
        )
        val exact = fs(p)
        val relaxed = fs(p, MarkSetOptions(relaxed = true))
        assertFalse(exact.applicable.get(1))
        assertTrue(relaxed.applicable.get(1))
    }
}
