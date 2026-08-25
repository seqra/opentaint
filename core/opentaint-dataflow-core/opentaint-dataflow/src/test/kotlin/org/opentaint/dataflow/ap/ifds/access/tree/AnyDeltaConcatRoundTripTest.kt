package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * The summary-application round trip on an `[any]`-carrying fact, and why it is a ratchet.
 *
 * Caller fact `arg0.[any].*`, summary `arg0.a.* -> ret.a.*`. Applying it runs two operations:
 *
 *  1. `delta(arg0.a)` walks the fact down the premise with `getChildRecording`. The
 *     `isCoveredByAny` arm of [AccessTree.AccessNode.getChild] rebuilds the `[any]` edge and
 *     returns the node it read FROM, so the read **consumes nothing** and the remainder is still
 *     `[any].*`.
 *  2. `concat` attaches that remainder at the conclusion's abstract node, below the concrete `a`
 *     the conclusion supplies.
 *
 * Net: `ret.a.[any].*` -- one concrete link longer than the fact went in, and still carrying an
 * `[any]`, so the next summary application does it again. The premise never makes progress against
 * the fact, but the fact gains a link every lap. That is the mechanism behind the deep concrete
 * chains in the conductor dumps, and it is the fallback the `[any]` unroll normally pre-empts.
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
    private fun openFact(base: AccessPathBase, vararg accessors: Accessor): FinalFactAp {
        var f = manager.mostAbstractFinalAp(base)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return f
    }

    private fun premise(base: AccessPathBase, vararg accessors: Accessor): InitialFactAp {
        var p = manager.mostAbstractInitialAp(base)
        accessors.reversed().forEach { p = p.prependAccessor(it) }
        return p
    }

    private fun FinalFactAp.render(): String = toString().replace('\n', ' ').trim()

    @Test
    fun `reading a concrete accessor off an any-carrying fact consumes nothing`() {
        val fact = openFact(arg0, AnyAccessor)          // arg0.[any].*
        val deltas = fact.delta(premise(arg0, A))       // premise arg0.a

        assertEquals(1, deltas.size, "expected a single remainder, got ${deltas.size}")

        // The remainder is the fact's own `[any]` subtree, rebuilt -- not the fact advanced past `a`.
        val remainder = deltas.single()
        assertTrue(
            remainder.toString().contains("[any]"),
            "the remainder must still carry the [any]; got $remainder"
        )
    }

    @Test
    fun `the round trip returns a fact one concrete link longer, still carrying the any`() {
        val fact = openFact(arg0, AnyAccessor)          // arg0.[any].*
        val conclusion = openFact(ret, A)               // ret.a.*
        val delta = fact.delta(premise(arg0, A)).single()

        val result = conclusion.concat(FactTypeChecker.Dummy, delta)
        assertTrue(result != null, "the graft must produce a fact")

        assertEquals(
            openFact(ret, A, AnyAccessor).render(), result!!.render(),
            "expected ret.a.[any].* -- the conclusion's concrete link in front of the surviving [any]"
        )
    }

    @Test
    fun `the round trip is a ratchet - one concrete link per lap and the any never leaves`() {
        // Each lap models one summary application. The premise is the chain the abstraction has
        // already emitted for this fact plus ONE more accessor -- the next rung of a field-read
        // ladder -- and the conclusion supplies that same chain. Four DISTINCT fields, because
        // `limitFieldAccess` folds a repeat and would mask the growth.
        val fields = listOf(A, B, C, D)
        var chain = emptyList<Accessor>()
        var fact = openFact(arg0, AnyAccessor)                 // arg0.[any].*

        val depths = mutableListOf(fact.depth)
        val shapes = mutableListOf(fact.render())

        for ((lap, next) in fields.withIndex()) {
            val premiseChain = chain + next
            val deltas = fact.delta(premise(arg0, *premiseChain.toTypedArray()))
            val delta = deltas.singleOrNull()
                ?: error("lap $lap: expected one remainder, got ${deltas.size}; fact=${fact.render()}")

            // The premise nominally consumed `premiseChain`, but the last step went through the
            // `[any]` and consumed nothing, so the remainder still carries it.
            assertTrue(
                delta.toString().contains("[any]"),
                "lap $lap: the [any] must survive the read; remainder=$delta"
            )

            val conclusion = openFact(arg0, *premiseChain.toTypedArray())
            fact = conclusion.concat(FactTypeChecker.Dummy, delta)
                ?: error("lap $lap: the graft returned null")

            chain = premiseChain
            depths += fact.depth
            shapes += fact.render()
        }

        assertTrue(
            shapes.all { it.contains("[any]") },
            "the [any] must survive every lap; shapes=$shapes"
        )
        assertTrue(
            depths.zipWithNext().all { (a, b) -> b > a },
            "each lap must deepen the fact; depths=$depths shapes=$shapes"
        )
        // The final fact spells the whole enumerated chain in front of an [any] that is exactly as
        // unspent as it was at the start.
        assertEquals(
            openFact(arg0, A, B, C, D, AnyAccessor).render(), fact.render(),
            "expected arg0.a.b.c.d.[any].*; shapes=$shapes"
        )
    }
}
