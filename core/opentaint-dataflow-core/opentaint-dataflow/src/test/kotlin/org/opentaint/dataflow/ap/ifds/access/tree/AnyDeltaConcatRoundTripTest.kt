package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

/**
 * The summary-application round trip on an `[any]`-carrying fact, and why it is no longer a ratchet.
 *
 * This file used to PIN the ratchet. Caller fact `arg0.[any].*`, summary `arg0.a.* -> ret.a.*`:
 *
 *  1. `delta(arg0.a)` walked the fact down the premise with the synthesising reader, whose
 *     `isCoveredByAny` term rebuilt the `[any]` edge and returned the node it read FROM -- so the
 *     read **consumed nothing** and the remainder was still `[any].*`;
 *  2. `concat` hung that remainder at the conclusion's abstract node, below the concrete `a`.
 *
 * Net `ret.a.[any].*`: one concrete link longer than the fact went in, still carrying an `[any]`, so
 * the next summary application did it again. A link a lap, forever.
 *
 * [TreeApManager.literalAnyMatch] removes step 1's third term. A premise link now matches only a
 * LITERAL child of the fact node, or a child sitting directly under that node's `[any]` edge
 * (`[any]` taken zero times) -- both of which strictly DESCEND the fact. So a premise can no longer
 * be consumed for free, `delta(arg0.[any].*, arg0.a)` is empty, and there is nothing to graft.
 *
 * The tests below pin all four halves of that: the refusal, the absence of a graft, the flat depth
 * sequence over four laps, and -- as the control that keeps the change attributable -- the OLD
 * ratchet, still exactly reproducible by constructing a manager with `literalAnyMatch = false`.
 *
 * Design: `docs/superpowers/specs/2026-08-27-literal-any-matching-design.md`.
 */
class AnyDeltaConcatRoundTripTest {

    private companion object {
        val A = FieldAccessor("N", "a", "N")
        val B = FieldAccessor("N", "b", "N")
        val C = FieldAccessor("N", "c", "N")
        val D = FieldAccessor("N", "d", "N")
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation(), -1)
    private val arg0 = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return

    /** `base.<accessors>.*` -- open at the leaf, the shape a caller fact and a conclusion both have. */
    private fun openFact(base: AccessPathBase, vararg accessors: Accessor): FinalFactAp =
        openFact(manager, base, *accessors)

    private fun premise(base: AccessPathBase, vararg accessors: Accessor): InitialFactAp =
        premise(manager, base, *accessors)

    private fun openFact(m: TreeApManager, base: AccessPathBase, vararg accessors: Accessor): FinalFactAp {
        var f = m.mostAbstractFinalAp(base)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return f
    }

    private fun premise(m: TreeApManager, base: AccessPathBase, vararg accessors: Accessor): InitialFactAp {
        var p = m.mostAbstractInitialAp(base)
        accessors.reversed().forEach { p = p.prependAccessor(it) }
        return p
    }

    private fun FinalFactAp.render(): String = toString().replace('\n', ' ').trim()

    /* ---------- what the rule refuses ---------- */

    @Test
    fun `a concrete premise does not match a fact that only reaches it through an any`() {
        val fact = openFact(arg0, AnyAccessor)          // arg0.[any].*

        assertEquals(
            emptyList(), fact.delta(premise(arg0, A)),
            "arg0.a must not be matched by synthesising `a` out of the [any]"
        )
    }

    /**
     * The case named in the design: a premise that is BOTH longer than the fact and carries an
     * `[any]` of its own. It fails at the first link, before the `[any]` is ever reached.
     */
    @Test
    fun `an any-carrying premise below a concrete link does not match either`() {
        val fact = openFact(arg0, AnyAccessor)          // arg0.[any].*

        assertEquals(
            emptyList(), fact.delta(premise(arg0, A, AnyAccessor)),
            "arg0.f.[any] must not match arg0.[any].*"
        )
    }

    @Test
    fun `with no delta there is nothing to graft, so the round trip cannot start`() {
        val fact = openFact(arg0, AnyAccessor)          // arg0.[any].*
        val conclusion = openFact(ret, A)               // ret.a.*

        val deltas = fact.delta(premise(arg0, A))
        assertTrue(deltas.isEmpty(), "precondition: the premise is refused; got $deltas")

        // Nothing to hand `concat`, so `ret.a.[any].*` -- the fact one concrete link longer that
        // used to come back out -- is not constructible from this pair at all.
        assertEquals(
            openFact(ret, A).render(), conclusion.render(),
            "the conclusion is applied unchanged or not at all; it never gains the caller's [any]"
        )
    }

    /* ---------- what the rule still allows: the literal readings ---------- */

    /**
     * The rule is LITERAL, not "refuse everything". The premise that names the `[any]` as a link
     * matches it, and matches it exactly -- the fact is spent, so the delta is empty and the
     * conclusion applies as it stands.
     */
    @Test
    fun `the premise that names the any consumes it`() {
        val fact = openFact(arg0, AnyAccessor)          // arg0.[any].*

        val delta = fact.delta(premise(arg0, AnyAccessor)).singleOrNull()
            ?: error("arg0.[any] must match arg0.[any].*")

        assertTrue(delta.isEmpty, "the fact is fully consumed, so the remainder is empty; got $delta")
    }

    /**
     * The zero-step reading, which is kept and is load-bearing: `[any]` denotes ZERO or more covered
     * steps, so a child sitting directly under the `[any]` edge really is at the prefix above it.
     *
     * R3b of [TreeInitialFactAbstraction] emits `p.u` for a taint mark inside an `[any]` subtree and
     * relies on exactly this hoist to match the fact that produced it; R3b off is measured at
     * conductor `Total vulnerabilities: 2 -> 0`. Unlike the term this design removes, it DESCENDS --
     * which is why it cannot re-arm anything.
     */
    @Test
    fun `a child under the any is matched at the prefix above it, and the read descends`() {
        val fact = openFact(arg0, AnyAccessor, A, B)    // arg0.[any].a.b.*

        val delta = fact.delta(premise(arg0, A)).singleOrNull()
            ?: error("the zero-step reading of [any] must match arg0.a")

        assertTrue(!delta.isEmpty, "there is a `b.*` left below `a`; got $delta")
        assertTrue(
            !delta.toString().contains("[any]"),
            "the read CONSUMED the [any] rather than re-installing it -- that is the progress the " +
                "old third term did not make; remainder=$delta"
        )

        // ... and the graft therefore relocates a strictly smaller remainder, once.
        val grafted = assertNotNull(openFact(ret, C).concat(FactTypeChecker.Dummy, delta))
        assertEquals(
            openFact(ret, C, B).render(), grafted.render(),
            "expected ret.c.b.* -- the conclusion's link in front of what was left below `a`"
        )
    }

    /* ---------- the ratchet, and its control ---------- */

    /**
     * Four laps of the loop that used to add a concrete link each time. The premise is the chain the
     * abstraction has already emitted for this fact plus ONE more accessor -- the next rung of a
     * field-read ladder -- and the conclusion supplies that same chain. Four DISTINCT fields,
     * because `limitFieldAccess` folds a repeat and would mask any growth.
     *
     * Now the very first lap has no delta, so the fact never moves.
     */
    @Test
    fun `there is no ratchet - the fact cannot gain a link on any lap`() {
        var chain = emptyList<Accessor>()
        val fact = openFact(arg0, AnyAccessor)                 // arg0.[any].*

        for ((lap, next) in listOf(A, B, C, D).withIndex()) {
            val premiseChain = chain + next
            assertEquals(
                emptyList(), fact.delta(premise(arg0, *premiseChain.toTypedArray())),
                "lap $lap: ${premiseChain.joinToString(".")} must not match ${fact.render()}"
            )
            chain = premiseChain
        }

        assertEquals(
            openFact(arg0, AnyAccessor).render(), fact.render(),
            "the fact is exactly what it was four laps ago"
        )
    }

    /**
     * The CONTROL, and the reason this file still describes the ratchet at all: with
     * `literalAnyMatch = false` the old engine is reproduced exactly, ratchet and all. Without this
     * the four tests above would pass just as well if `delta` had been broken outright, and the A/B
     * on the harness would have no unit-level statement.
     *
     * `anyUnrollLimit = -1` so the `[any]` unroll manager is off and cannot absorb the step back.
     */
    @Test
    fun `the old reader still ratchets, which is what makes the new one attributable`() {
        val m = TreeApManager(UnrollStrategy, RefManager(), Cancellation(), -1, literalAnyMatch = false)

        var chain = emptyList<Accessor>()
        var fact = openFact(m, arg0, AnyAccessor)              // arg0.[any].*

        val depths = mutableListOf(fact.depth)
        val shapes = mutableListOf(fact.render())

        for ((lap, next) in listOf(A, B, C, D).withIndex()) {
            val premiseChain = chain + next
            val delta = fact.delta(premise(m, arg0, *premiseChain.toTypedArray())).singleOrNull()
                ?: error("lap $lap: expected one remainder, got none; fact=${fact.render()}")

            assertTrue(
                delta.toString().contains("[any]"),
                "lap $lap: the old read consumes nothing, so the [any] survives; remainder=$delta"
            )

            fact = openFact(m, arg0, *premiseChain.toTypedArray()).concat(FactTypeChecker.Dummy, delta)
                ?: error("lap $lap: the graft returned null")

            chain = premiseChain
            depths += fact.depth
            shapes += fact.render()
        }

        assertTrue(
            depths.zipWithNext().all { (a, b) -> b > a },
            "each lap deepens the fact under the old reader; depths=$depths shapes=$shapes"
        )
        assertEquals(
            openFact(m, arg0, A, B, C, D, AnyAccessor).render(), fact.render(),
            "expected arg0.a.b.c.d.[any].* -- the whole chain in front of an unspent [any]; shapes=$shapes"
        )
    }

    /**
     * The `[any]` unroll manager used to be the thing that closed this loop: at `L = 0` a spent pot
     * absorbed the prepended step back into the `[any]`, and the ratchet became a loop rather than a
     * climb. Under the literal rule the outcome does not depend on `L` at all, because no lap ever
     * starts -- which is the unit-level statement of the design's claim that the manager is bounding
     * a mechanism that no longer runs.
     */
    @Test
    fun `the outcome no longer depends on the unroll budget`() {
        for (limit in listOf(-1, 0, 1, 100)) {
            val m = TreeApManager(UnrollStrategy, RefManager(), Cancellation(), limit)
            assertEquals(
                emptyList(), openFact(m, arg0, AnyAccessor).delta(premise(m, arg0, A)),
                "L=$limit must make no difference: the premise is refused before any budget is consulted"
            )
        }
    }
}
