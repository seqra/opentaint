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
 * The SIZE of the premise population an `[any]`-carrying fact generates, and what bounds it.
 *
 * `AnyPremiseAbstractionTest` pins what a single `[any]` fact emits. This pins what happens when the
 * emissions come BACK as refined premises, which is the loop the engine actually runs and the one
 * that decides how much work a fact costs.
 *
 * **This file used to record a `Σ n!/(n−k)!` fixed point — 4, 15, 64 premises for demand sets of
 * 2, 3, 4 — and it recorded it TWICE.** Once when the population was built by
 * `unrollAnyAccessors` re-rooting the `[any]`-carrying carrier, and again, unchanged, after
 * never-unroll deleted that copy: R3c handed out `p.a`, R4 descended into it through `getChild`'s
 * synthesis term, the caller refined it, R3c handed out `p.a.b`. Never-unroll removed the fact
 * materialisation and not the premise enumeration, and this test is where that showed.
 *
 * [TreeApManager.literalAnyMatch] removes the enumeration. R3c and R4 are gone and the matching
 * reader no longer synthesises, so a fact's premises are exactly its LITERAL PREFIXES:
 *
 * ```
 * fact  this.a.[any].*      premises = { this , this.a , this.a.[any] }
 * ```
 *
 * — three, whatever the demand set contains. The old superexponential shape is still reachable, and
 * is still asserted here, by constructing the manager with `literalAnyMatch = false`; that control
 * is what keeps the new numbers attributable to the rule rather than to a broken walk.
 *
 * Design: `docs/superpowers/specs/2026-08-27-literal-any-matching-design.md`.
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

    /**
     * One manager, one abstraction and the builders that go with them.
     *
     * A class rather than fields because the whole point of several tests below is to run the SAME
     * drive under both readings of `[any]`, and the reading is fixed at manager construction.
     * `anyUnrollLimit = -1` throughout: the `[any]` unroll manager is off, so nothing here is
     * measuring a budget.
     */
    private class Harness(literalAnyMatch: Boolean = true) {
        val manager = TreeApManager(
            UnrollStrategy, RefManager(), Cancellation(), -1, literalAnyMatch = literalAnyMatch,
        )
        val base = AccessPathBase.This

        fun abstraction() = TreeInitialFactAbstraction(manager)

        fun premise(vararg accessors: Accessor): InitialFactAp {
            var ap = manager.mostAbstractInitialAp(base)
            accessors.reversed().forEach { ap = ap.prependAccessor(it) }
            return ap
        }

        /** `<this>.<accessors>.$` -- closed at the leaf. */
        fun fact(vararg accessors: Accessor): FinalFactAp {
            var f = manager.createFinalAp(base, ExclusionSet.Empty)
            accessors.reversed().forEach { f = f.prependAccessor(it) }
            return f
        }

        /** `<this>.<accessors>.*` -- open at the leaf, the shape a caller fact has. */
        fun openFact(vararg accessors: Accessor): FinalFactAp {
            var f = manager.mostAbstractFinalAp(base)
            accessors.reversed().forEach { f = f.prependAccessor(it) }
            return f
        }
    }

    private fun InitialFactAp.excluding(vararg accessors: Accessor): InitialFactAp {
        var ap = this
        accessors.forEach { ap = ap.exclude(it) }
        return ap
    }

    private fun TreeInitialFactAbstraction.register(ap: InitialFactAp) =
        registerNewInitialFact(ap, FactTypeChecker.Dummy)

    private fun TreeInitialFactAbstraction.add(f: FinalFactAp) =
        addAbstractedInitialFact(f, FactTypeChecker.Dummy)

    private fun List<Pair<InitialFactAp, FinalFactAp>>.premises(): List<InitialFactAp> = map { it.first }

    /** The accessor chain of a premise, rendered as `a.b.c`, for readable assertions. */
    private fun InitialFactAp.chain(): String =
        toString().substringAfter("<this>").removePrefix(".").substringBefore("/").trim()

    /* ---------- 1: the invariant, stated ---------- */

    /**
     * The design's headline claim, verbatim: a fact `a.f.[any].*` has three premises, and they are
     * its three literal prefixes.
     *
     * The drive is the ladder the engine actually walks -- emit, let the callee refine, emit again --
     * so the assertion is over every premise the walk EVER hands out, not over one call's output.
     */
    @Test
    fun `a fact's premises are exactly its literal prefixes`() {
        val h = Harness()
        val abstraction = h.abstraction()
        val emitted = linkedSetOf<InitialFactAp>()

        // R0: no demand anywhere yet, so the bare base premise, whose `.*` covers everything.
        emitted += abstraction.add(h.openFact(A, AnyAccessor)).premises()          // this.a.[any].*
        // The callee refines it: demand for every field at the root. R2 answers with the one the
        // fact holds literally.
        emitted += abstraction.register(h.premise().excluding(*FIELDS.toTypedArray())).premises()
        // ... and again one level down, where R3a answers with the coarse edge.
        emitted += abstraction.register(h.premise(A).excluding(B)).premises()

        // `.*` is the premise's completion, not a link: `a.*` IS the premise `<this>.a`.
        assertEquals(
            listOf("*", "a.*", "a.[any].*"), emitted.map { it.chain() },
            "expected exactly <this>, <this>.a and <this>.a.[any] -- the fact's literal prefixes"
        )
    }

    /* ---------- 2: what the ladder used to do at each rung ---------- */

    /**
     * R3c's rung. A demanded accessor the fact reaches ONLY through its `[any]` no longer gets a
     * premise of its own; R3a's coarse `p.[any]` answers the whole level, and its entry fact
     * `p.[any].*` subsumes every `p.a.*` that was asked for.
     */
    @Test
    fun `a demanded accessor reached only through the any gets no premise of its own`() {
        val h = Harness()
        val abstraction = h.abstraction()
        abstraction.register(h.premise().excluding(A, B))

        val produced = abstraction.add(h.fact(AnyAccessor, MARK)).premises()       // this.[any].!m.$

        assertTrue(
            h.premise(AnyAccessor) in produced,
            "the coarse edge answers the level; produced=${produced.map { it.chain() }}"
        )
        assertTrue(
            h.premise(A) !in produced && h.premise(B) !in produced,
            "neither `a` nor `b` may be named -- the fact holds them nowhere literally; " +
                "produced=${produced.map { it.chain() }}"
        )
    }

    /**
     * R4's rung, which is the one that made the ladder a ladder. The premise R3c handed out
     * registered a trie node, and R4 routed the NEXT walk into it by reading the accessor out of the
     * `[any]`. Without both there is no second level to extend.
     */
    @Test
    fun `there is no second level - the walk is never routed below a premise the fact does not hold`() {
        val h = Harness()
        val abstraction = h.abstraction()
        abstraction.register(h.premise().excluding(A, B))
        abstraction.add(h.fact(AnyAccessor, MARK))

        val second = abstraction.register(h.premise(A).excluding(B)).premises()

        assertTrue(
            h.premise(A, B) !in second,
            "`a.b` needs R4 to descend into a node the fact never had; produced=${second.map { it.chain() }}"
        )
        assertTrue(
            second.none { it.chain().split('.').any { link -> link == "a" || link == "b" } },
            "no concrete field may appear at any depth; produced=${second.map { it.chain() }}"
        )
    }

    /**
     * `limitFieldAccess` forbids a field repeating on one path, and it used to be the ONLY thing
     * bounding the enumeration -- at `N!` rather than at infinity. It is now subsumed several times
     * over (nothing concrete is enumerated at all), and the assertion is kept as a guard: if the
     * ladder ever comes back, this is the shape that says it came back without even that bound.
     */
    @Test
    fun `a repeated accessor is not enumerated`() {
        val h = Harness()
        val abstraction = h.abstraction()
        abstraction.register(h.premise().excluding(A, B))
        abstraction.add(h.fact(AnyAccessor, MARK))

        val second = abstraction.register(h.premise(A).excluding(A, B)).premises()

        assertTrue(
            h.premise(A, A) !in second,
            "a.a must not be enumerated; produced=${second.map { it.chain() }}"
        )
    }

    /* ---------- 3: the population, and the control ---------- */

    /**
     * Drives the loop `MethodAnalyzer` closes: every premise the abstraction emits is handed to a
     * callee, refined there, and comes back through `handleInputFactChange` ->
     * `registerNewInitialFact` carrying a non-empty exclusion set. Here the refinement is the
     * strongest one a field-read ladder can produce: every field not already on the path.
     */
    private fun driveToClosure(h: Harness, fields: List<FieldAccessor>): Set<InitialFactAp> {
        val abstraction = h.abstraction()
        val seen = linkedSetOf<InitialFactAp>()
        val work = ArrayDeque<Pair<InitialFactAp, List<FieldAccessor>>>()

        abstraction.register(h.premise().excluding(*fields.toTypedArray()))
        abstraction.add(h.fact(AnyAccessor, MARK)).premises().forEach {
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
    fun `the demand set no longer grows the premise population`() {
        val counts = (2..4).map { n -> driveToClosure(Harness(), FIELDS.take(n)).size }

        assertEquals(
            listOf(counts.first(), counts.first(), counts.first()), counts,
            "the population must not depend on the demand set at all; " +
                "the same drive used to give ${(2..4).map { sequences(it) }}, got $counts"
        )
    }

    @Test
    fun `no premise in the closure names an accessor the fact does not hold`() {
        for (n in 2..4) {
            // `chain()` renders the premise's `.*` completion, so the BASE premise is `*`, not "".
            val concrete = driveToClosure(Harness(), FIELDS.take(n))
                .filterNot { it.chain() == "*" || it.chain().contains("[any]") }

            assertEquals(
                emptyList(), concrete.map { it.chain() }.sorted(),
                "N=$n: the fact is `this.[any].!m` and holds no field literally, so no field may be " +
                    "named; the old ladder produced ${sequences(n)} such premises here"
            )
        }
    }

    /**
     * The CONTROL. `literalAnyMatch = false` reproduces the old engine exactly, `Σ n!/(n−k)!` and
     * all -- so the two tests above are measuring the rule and not a walk that stopped working.
     *
     * Kept as a live assertion rather than a comment because the numbers 4/15/64 are the whole
     * reason this file exists, and because R3c/R4 still ship behind the flag.
     */
    @Test
    fun `the old reader still enumerates every non-repeating sequence over the demand set`() {
        for (n in 2..4) {
            val produced = driveToClosure(Harness(literalAnyMatch = false), FIELDS.take(n))
            val concrete = produced.filterNot { it.chain() == "*" || it.chain().contains("[any]") }

            assertEquals(
                sequences(n), concrete.size,
                "N=$n: expected every non-repeating sequence over $n accessors " +
                    "(sum n!/(n-k)! = ${sequences(n)}), got ${concrete.size}: " +
                    concrete.map { it.chain() }.sorted()
            )
        }
    }

    @Test
    fun `the old reader's growth is superexponential and the new one's is flat`() {
        val old = (2..4).map { n -> driveToClosure(Harness(literalAnyMatch = false), FIELDS.take(n)).size }
        val new = (2..4).map { n -> driveToClosure(Harness(), FIELDS.take(n)).size }

        assertTrue(
            old.zipWithNext().all { (a, b) -> b > a * 2 },
            "the old reader must still grow superexponentially, got $old"
        )
        assertTrue(
            new.zipWithNext().all { (a, b) -> b == a },
            "the new reader must not grow at all, got $new"
        )
        assertTrue(
            new.last() < old.last(),
            "and the new population must be smaller: new=$new old=$old"
        )
    }
}
