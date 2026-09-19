package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * `containsAccessorDeep` must answer exactly `getAllAccessors().contains(_)`.
 *
 * It exists because the set version costs the tree's PATH count -- `collectAccessorsTo` recurses
 * with no memo over what interning and `mergeAdd`'s result memo make a DAG -- and allocates two
 * sets plus an interner lookup per accessor, all to answer one membership question. The predicate
 * is the contract; this pins it on merged, shared, `[any]`-bearing trees, where the two walks
 * would differ if the memo skipped a node it should have entered.
 */
class AccessNodeContainsAccessorDeepTest {

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())
    private val base = AccessPathBase.This

    private val fields = (0 until 6).map { FieldAccessor("C$it", "f$it", "C${(it + 1) % 6}") }
    private val marks = (0 until 3).map { TaintMarkAccessor("m$it") }

    /** What may appear at a non-terminal position: a mark only attaches to the leaf. */
    private val inner: List<Accessor> = fields + listOf(ElementAccessor, AnyAccessor)

    /** Every accessor the predicate is asked about, including ones absent from the tree. */
    private val probes: List<Accessor> =
        inner + marks + FinalAccessor + FieldAccessor("Z", "absent", "Z") + TaintMarkAccessor("absent")

    /** `prefix` then an optional trailing mark, over a final leaf. */
    private fun chain(prefix: List<Accessor>, mark: TaintMarkAccessor? = null): FinalFactAp {
        var fact = manager.createFinalAp(base, ExclusionSet.Empty)
        if (mark != null) fact = fact.prependAccessor(mark)
        for (accessor in prefix.reversed()) {
            fact = fact.prependAccessor(accessor)
        }
        return fact
    }

    private fun assertAgrees(fact: FinalFactAp) {
        val all = fact.getAllAccessors()
        for (probe in probes) {
            assertEquals(
                all.contains(probe), fact.containsAccessorDeep(probe),
                "disagreement on $probe for $fact"
            )
        }
    }

    private fun randomChain(random: Random): FinalFactAp = chain(
        List(1 + random.nextInt(5)) { inner[random.nextInt(inner.size)] },
        marks.getOrNull(random.nextInt(marks.size + 1))
    )

    @Test
    fun `agrees on single chains`() {
        for (seed in 0 until 300) {
            assertAgrees(randomChain(Random(seed)))
        }
    }

    @Test
    fun `agrees on merged trees with shared subtrees`() {
        for (seed in 0 until 150) {
            val random = Random(seed)

            // A shared tail prepended under several different prefixes: the merge result reuses the
            // same node object under many parents, which is the DAG the memo has to handle.
            val tailMark = marks[random.nextInt(marks.size)]
            val tail = List(1 + random.nextInt(3)) { inner[random.nextInt(inner.size)] }

            var merged = randomChain(random)
            repeat(4) {
                val prefix = List(1 + random.nextInt(3)) { inner[random.nextInt(inner.size)] }
                merged = merge(merged, chain(prefix + tail, tailMark))
            }

            assertAgrees(merged)
        }
    }

    @Test
    fun `agrees on deep self-similar shapes`() {
        // The shape the unfold demand actually walks: one field repeated, with an `[any]` and a
        // mark at the bottom, merged with its own prefixes so nodes are shared at every level.
        val f = fields[0]
        var fact = chain(List(12) { f }, marks[0])
        for (depth in 1 until 12) {
            fact = merge(fact, chain(List(depth) { f } + AnyAccessor, marks[1]))
        }

        assertTrue(fact.getAllAccessors().contains(marks[0]), "the fixture lost its mark")
        assertAgrees(fact)
    }

    private fun merge(left: FinalFactAp, right: FinalFactAp): FinalFactAp {
        left as AccessTree
        right as AccessTree
        return AccessTree(manager, base, left.access.mergeAdd(right.access, foldToAny = false), ExclusionSet.Empty)
    }
}
