package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * The SHAPE of `[any]` unroll growth: which operation manufactures the nodes, and what the fixed
 * point of doing it repeatedly is.
 *
 * `AnyPremiseAbstractionTest` pins what a single `[any]` fact emits. This pins what happens when the
 * emissions come BACK as refined premises, which is the loop the engine actually runs and the one
 * that decides how large a fact gets. Three claims, in order:
 *
 *  1. one unroll level offers one premise per demanded accessor;
 *  2. the object the unroll re-roots is the `[any]`-CARRYING node, so the copy carries an `[any]`
 *     again and the next level can extend it;
 *  3. closing the loop the way `MethodAnalyzer.handleInputFactChange` does enumerates every
 *     non-repeating sequence over the demand set -- `Σ_{k=1..N} N!/(N−k)!`, i.e. Θ(e·N!).
 *
 * Deliberately run against [FactTypeChecker.Dummy]. That is not a convenience: it is exactly the
 * state the real type checker is in once a path has crossed a `java.lang.Object`-typed edge, where
 * `typeMayHaveSubtypeOf` returns `true` unconditionally. On conductor 99.6% of the largest fact sits
 * below such an edge, so "the filter accepts everything" is the measured case, not a degenerate one.
 */
class AnyUnrollGrowthPatternTest {

    private companion object {
        /** Self-typed so that any chain over them is type-feasible for a real checker too. */
        val FIELDS = listOf(
            FieldAccessor("N", "a", "N"),
            FieldAccessor("N", "b", "N"),
            FieldAccessor("N", "c", "N"),
            FieldAccessor("N", "d", "N"),
        )
        val A = FIELDS[0]
        val B = FIELDS[1]
        val MARK = TaintMarkAccessor("test-mark")

        /** `Σ_{k=1..n} n!/(n−k)!` — the number of non-empty non-repeating sequences over `n` items. */
        fun sequences(n: Int): Int {
            var total = 0
            var falling = 1
            for (k in 1..n) {
                falling *= (n - k + 1)
                total += falling
            }
            return total
        }
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation(), -1)
    private val base = AccessPathBase.This

    private fun abstraction() = TreeInitialFactAbstraction(manager)

    private fun premise(vararg accessors: Accessor): InitialFactAp {
        var ap = manager.mostAbstractInitialAp(base)
        accessors.reversed().forEach { ap = ap.prependAccessor(it) }
        return ap
    }

    private fun InitialFactAp.excluding(vararg accessors: Accessor): InitialFactAp {
        var ap = this
        accessors.forEach { ap = ap.exclude(it) }
        return ap
    }

    private fun fact(vararg accessors: Accessor): FinalFactAp {
        var f = manager.createFinalAp(base, ExclusionSet.Empty)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return f
    }

    private fun TreeInitialFactAbstraction.register(ap: InitialFactAp) =
        registerNewInitialFact(ap, FactTypeChecker.Dummy)

    private fun TreeInitialFactAbstraction.add(f: FinalFactAp) =
        addAbstractedInitialFact(f, FactTypeChecker.Dummy)

    private fun List<Pair<InitialFactAp, FinalFactAp>>.premises(): List<InitialFactAp> = map { it.first }

    /** The accessor chain of a premise, rendered as `a.b.c`, for readable assertions. */
    private fun InitialFactAp.chain(): String =
        toString().substringAfter("<this>").removePrefix(".").substringBefore("/").trim()

    /* ---------- 1: one premise per demanded accessor ---------- */

    @Test
    fun `one unroll level offers exactly one premise per demanded accessor`() {
        val abstraction = abstraction()
        // Demand at the root: two accessors were excluded there, so both are offered to the unroll.
        abstraction.register(premise().excluding(A, B))

        val produced = abstraction.add(fact(AnyAccessor, MARK)).premises()

        assertTrue(premise(A) in produced, "expected the `a` unroll; produced=${produced.map { it.chain() }}")
        assertTrue(premise(B) in produced, "expected the `b` unroll; produced=${produced.map { it.chain() }}")
    }

    /* ---------- 2: the copy carries the `[any]` again ---------- */

    @Test
    fun `the unroll re-roots the any-carrying node, so the copy can be unrolled again`() {
        val abstraction = abstraction()
        abstraction.register(premise().excluding(A, B))
        abstraction.add(fact(AnyAccessor, MARK))

        // If the unroll had copied only the `[any]` SUBTREE, `this.a` would hold `![mark]` and
        // nothing else -- there would be no `[any]` under it and no second level to ask for. It
        // copies the CARRIER, so `this.a` owns an `[any]` of its own and demand registered there is
        // answered with a second accessor.
        val second = abstraction.register(premise(A).excluding(B)).premises()

        assertTrue(
            premise(A, B) in second,
            "expected `a.b` from unrolling the copy's own [any]; produced=${second.map { it.chain() }}"
        )
    }

    @Test
    fun `a repeated accessor is not enumerated`() {
        val abstraction = abstraction()
        abstraction.register(premise().excluding(A, B))
        abstraction.add(fact(AnyAccessor, MARK))

        val second = abstraction.register(premise(A).excluding(A, B)).premises()

        // `limitFieldAccess` forbids a field repeating on one path. That is the ONLY thing bounding
        // the enumeration below, and it bounds it at N! rather than at infinity.
        assertTrue(
            premise(A, A) !in second,
            "a.a must not be enumerated; produced=${second.map { it.chain() }}"
        )
    }

    /* ---------- 3: the fixed point ---------- */

    /**
     * Drives the loop `MethodAnalyzer` closes: every premise the abstraction emits is handed to a
     * callee, refined there, and comes back through `handleInputFactChange` ->
     * `registerNewInitialFact` carrying a non-empty exclusion set. Here the refinement is the
     * strongest one a field-read ladder can produce: every field not already on the path.
     */
    private fun driveToClosure(fields: List<FieldAccessor>): Set<InitialFactAp> {
        val abstraction = abstraction()
        val seen = linkedSetOf<InitialFactAp>()
        val work = ArrayDeque<Pair<InitialFactAp, List<FieldAccessor>>>()

        abstraction.register(premise().excluding(*fields.toTypedArray()))
        abstraction.add(fact(AnyAccessor, MARK)).premises().forEach {
            if (seen.add(it)) work.addLast(it to fields)
        }

        while (work.isNotEmpty()) {
            val (ap, remaining) = work.removeFirst()
            val chain = ap.chain().split('.').filter { it.isNotEmpty() }.toSet()
            val next = remaining.filter { it.fieldName !in chain }
            if (next.isEmpty()) continue
            abstraction.register(ap.excluding(*next.toTypedArray())).premises().forEach {
                if (seen.add(it)) work.addLast(it to next)
            }
        }
        return seen
    }

    @Test
    fun `the fixed point is every non-repeating sequence over the demand set`() {
        for (n in 2..4) {
            val test = AnyUnrollGrowthPatternTest()
            val produced = test.driveToClosure(FIELDS.take(n))
            val concrete = produced.filterNot { it.chain().contains("[any]") }

            assertEquals(
                sequences(n), concrete.size,
                "N=$n: expected every non-repeating sequence over $n accessors " +
                    "(sum n!/(n-k)! = ${sequences(n)}), got ${concrete.size}: " +
                    concrete.map { it.chain() }.sorted()
            )
        }
    }

    @Test
    fun `growth is superexponential in the size of the demand set`() {
        val counts = (2..4).map { n -> AnyUnrollGrowthPatternTest().driveToClosure(FIELDS.take(n)).size }

        // 4 -> 15 -> 64 for N = 2, 3, 4: each extra demanded accessor multiplies the premise
        // population by more than N, which is why a depth cap buys so little (see
        // `fact-explosion-mechanism`: at K=7 only 1.58x on ThingsBoard).
        assertTrue(
            counts.zipWithNext().all { (a, b) -> b > a * 2 },
            "expected superexponential growth, got $counts"
        )
    }
}
