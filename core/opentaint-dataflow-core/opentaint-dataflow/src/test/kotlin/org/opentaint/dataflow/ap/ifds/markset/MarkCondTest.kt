package org.opentaint.dataflow.ap.ifds.markset

import java.util.BitSet
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class MarkCondTest {
    private companion object {
        const val TRIAL_COUNT = 2000
        const val MAX_DEPTH = 4
        const val MARK_COUNT = 4
    }

    // ---- test-local DNF oracle -------------------------------------------
    //
    // Cubes are literal sets (`Set<Int>`); literal ids are encoded as
    // `mark * 2 + pos` (pos in 0..1), so the mark a literal names is
    // recoverable without a side table. `toDnf` mirrors the fold used by
    // `eval`/`MarkCond` itself: `And` folds from the unit cube (`True`),
    // `Or` folds from no cubes at all (`False`).

    private fun MarkCond.toDnf(): List<Set<Int>> = when (this) {
        MarkCond.True -> listOf(emptySet())
        MarkCond.False -> emptyList()
        is MarkCond.Lit -> listOf(setOf(literal))
        is MarkCond.And -> args.fold(listOf(emptySet<Int>())) { acc, arg -> dnfAnd(acc, arg.toDnf()) }
        is MarkCond.Or -> args.fold(emptyList<Set<Int>>()) { acc, arg -> acc + arg.toDnf() }
    }

    private fun dnfAnd(a: List<Set<Int>>, b: List<Set<Int>>): List<Set<Int>> =
        a.flatMap { ca -> b.map { cb -> ca + cb } }

    /** Literal ids are encoded as `mark * 2 + pos`, so the mark is recoverable. */
    private fun literalMark(literal: Int): Int = literal / 2

    private fun Set<Int>.containedIn(marks: Set<Int>): Boolean = all { literalMark(it) in marks }

    private fun dnfSat(dnf: List<Set<Int>>, marks: Set<Int>): Boolean = dnf.any { it.containedIn(marks) }

    private fun dnfSmallSat(dnf: List<Set<Int>>, marks: Set<Int>): Boolean =
        dnf.any { it.size <= 1 && it.containedIn(marks) }

    private fun dnfBig(dnf: List<Set<Int>>, marks: Set<Int>): Boolean =
        dnf.any { it.size >= 2 && it.containedIn(marks) }

    private fun dnfSingles(dnf: List<Set<Int>>, marks: Set<Int>): Set<Int> =
        dnf.filter { it.size == 1 }.map { it.single() }.filter { literalMark(it) in marks }.toSet()

    // ---- random tree generator (seeded, depth <= 4, <= 4 marks) -----------

    private fun randomLeaf(random: Random): MarkCond = when (random.nextInt(3)) {
        0 -> MarkCond.True
        1 -> MarkCond.False
        else -> {
            val mark = random.nextInt(MARK_COUNT)
            val pos = random.nextInt(2)
            MarkCond.Lit(mark, mark * 2 + pos)
        }
    }

    private fun randomCond(random: Random, depth: Int): MarkCond {
        if (depth == 0) return randomLeaf(random)
        return when (random.nextInt(5)) {
            0 -> MarkCond.True
            1 -> MarkCond.False
            2 -> randomLeaf(random)
            3 -> {
                val arity = random.nextInt(2, 4)
                MarkCond.And((0 until arity).map { randomCond(random, depth - 1) })
            }
            else -> {
                val arity = random.nextInt(2, 4)
                MarkCond.Or((0 until arity).map { randomCond(random, depth - 1) })
            }
        }
    }

    private fun randomMarks(random: Random): Set<Int> =
        (0 until MARK_COUNT).filter { random.nextBoolean() }.toSet()

    private fun bitSetOf(marks: Set<Int>): BitSet {
        val bits = BitSet()
        marks.forEach { bits.set(it) }
        return bits
    }

    @Test
    fun `eval matches the DNF oracle on random trees`() {
        val random = Random(42)
        repeat(TRIAL_COUNT) {
            val cond = randomCond(random, MAX_DEPTH)
            val marks = randomMarks(random)
            val dnf = cond.toDnf()
            val actual = cond.eval(bitSetOf(marks))

            assertEquals(dnfSat(dnf, marks), actual.sat, "sat mismatch for $cond on $marks")
            assertEquals(dnfSmallSat(dnf, marks), actual.smallSat, "smallSat mismatch for $cond on $marks")
            assertEquals(dnfBig(dnf, marks), actual.big, "big mismatch for $cond on $marks")
            assertEquals(dnfSingles(dnf, marks), actual.singles, "singles mismatch for $cond on $marks")
        }
    }

    // ---- named witnesses from the Lean `Cond` module -----------------------

    @Test
    fun `naiveAny_unsound - a constant-true disjunct is satisfied on the empty mark set`() {
        val cond = MarkCond.Or(listOf(MarkCond.True, MarkCond.Lit(1, 10)))
        assertTrue(cond.eval(BitSet()).sat)
    }

    @Test
    fun `sat_not_join_distributive - a two-mark conjunction needs both marks together`() {
        val cond = MarkCond.And(listOf(MarkCond.Lit(1, 10), MarkCond.Lit(2, 20)))
        assertTrue(cond.eval(bitSetOf(setOf(1, 2))).sat)
        assertFalse(cond.eval(bitSetOf(setOf(1))).sat)
        assertFalse(cond.eval(bitSetOf(setOf(2))).sat)
    }

    @Test
    fun `tree_vs_dnf_cost - a chain of 12 binary disjunctions evaluates in linear time`() {
        val k = 12
        val cond = andOrChain(k)
        val allMarks = bitSetOf((0 until 2 * k).toSet())

        assertTrue(cond.eval(allMarks).sat)
        assertEquals(1 shl k, cond.toDnf().size)
    }

    /** `(a0 v b0) ^ (a1 v b1) ^ ... ^ true`, with `k` disjunctions (Lean `andOrChain`). */
    private fun andOrChain(k: Int): MarkCond {
        if (k == 0) return MarkCond.True
        val m0 = 2 * (k - 1)
        val m1 = 2 * (k - 1) + 1
        return MarkCond.And(
            listOf(
                MarkCond.Or(listOf(MarkCond.Lit(m0, m0), MarkCond.Lit(m1, m1))),
                andOrChain(k - 1),
            ),
        )
    }

    @Test
    fun `same literal twice in a conjunction is not joined`() {
        val cond = MarkCond.And(listOf(MarkCond.Lit(1, 99), MarkCond.Lit(1, 99)))
        val result = cond.eval(bitSetOf(setOf(1)))
        assertFalse(result.big)
        assertEquals(setOf(99), result.singles)
    }

    @Test
    fun `hasJoinedCube agrees with eval on the union of all atoms`() {
        val random = Random(7)
        repeat(200) {
            val cond = randomCond(random, MAX_DEPTH)
            assertEquals(cond.eval(cond.atoms()).big, cond.hasJoinedCube())
        }
    }
}
