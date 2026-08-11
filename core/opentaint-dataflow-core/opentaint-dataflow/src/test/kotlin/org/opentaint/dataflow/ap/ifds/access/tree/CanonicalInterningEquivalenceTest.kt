package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import org.opentaint.dataflow.ap.ifds.access.util.contentKey
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals

/**
 * The invariant behind deterministic trace fingerprints: everything derived from accessor
 * indices must be a function of accessor CONTENT, never of the order in which threads
 * happened to intern.
 *
 * Two halves, matching the two mechanisms on the branch:
 *  - canonical interning ([AccessorInterner.preIntern]): the index assignment itself is
 *    independent of the seed's collection order, and seeded indices survive later
 *    stragglers regardless of straggler order;
 *  - content-ordered iteration ([TreeApManager.factContentKey] and the walk order behind
 *    it): even when two interners assign OPPOSITE indices, the canonical fact key -- which
 *    encodes child walk order -- is identical.
 */
class CanonicalInterningEquivalenceTest {

    private companion object {
        // Covers every dynamically interned kind, with several entries per kind so order
        // is observable, and field names of different lengths (FieldAccessor's comparator
        // orders by name length first).
        val UNIVERSE: List<Accessor> = listOf(
            FieldAccessor("com.a.Pair", "raw", "com.a.Box"),
            FieldAccessor("com.a.Pair", "value", "com.a.Box"),
            FieldAccessor("com.b.Box", "f", "java.lang.String"),
            FieldAccessor("com.b.Box", "aMuchLongerFieldName", "java.lang.String"),
            ClassStaticAccessor("com.a.Pair"),
            ClassStaticAccessor("com.b.Box"),
            TaintMarkAccessor("sqli"),
            TaintMarkAccessor("xss"),
            TypeInfoAccessor("com.a.Pair"),
            TypeInfoAccessor("com.b.Box"),
        )

        val STRAGGLERS: List<Accessor> = listOf(
            FieldAccessor("z.Late", "field", "z.T"),
            ClassStaticAccessor("z.Late"),
            TaintMarkAccessor("late-mark"),
            TypeInfoAccessor("z.Late"),
        )
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    @Test
    fun `preIntern assigns indices independent of seed collection order`() {
        val fwd = AccessorInterner().apply { preIntern(UNIVERSE) }
        val rev = AccessorInterner().apply { preIntern(UNIVERSE.reversed()) }
        val shuffled = AccessorInterner().apply { preIntern(UNIVERSE.shuffled(Random(42))) }
        for (accessor in UNIVERSE) {
            assertEquals(fwd.index(accessor), rev.index(accessor), "reversed seed moved $accessor")
            assertEquals(fwd.index(accessor), shuffled.index(accessor), "shuffled seed moved $accessor")
        }
    }

    @Test
    fun `seeded indices survive stragglers interned in any order`() {
        val a = AccessorInterner().apply { preIntern(UNIVERSE) }
        val b = AccessorInterner().apply { preIntern(UNIVERSE) }
        STRAGGLERS.forEach { a.index(it) }
        STRAGGLERS.reversed().forEach { b.index(it) }
        for (accessor in UNIVERSE) {
            assertEquals(a.index(accessor), b.index(accessor), "straggler interning moved seeded $accessor")
        }
    }

    @Test
    fun `fact content key is identical under opposite interning orders`() {
        // No seed at all: intern the universe directly, in opposite orders, so the two
        // managers hold genuinely different index assignments.
        fun managerInterning(order: List<Accessor>): TreeApManager =
            TreeApManager(UnrollStrategy, RefManager(), Cancellation()).also { m ->
                order.forEach { m.interner.index(it) }
            }

        val fwd = managerInterning(UNIVERSE)
        val rev = managerInterning(UNIVERSE.reversed())

        val moved = UNIVERSE.count { fwd.interner.index(it) != rev.interner.index(it) }
        assertNotEquals(0, moved, "index assignments must differ for this test to prove anything")

        fun multiBranchFact(manager: TreeApManager): AccessTree {
            val base = AccessPathBase.This
            fun chain(vararg accessors: Accessor): AccessTree {
                var fact = manager.createFinalAp(base, ExclusionSet.Empty)
                for (accessor in accessors.reversed()) fact = fact.prependAccessor(accessor)
                return fact as AccessTree
            }
            val branches = listOf(
                chain(UNIVERSE[0], UNIVERSE[6]),
                chain(UNIVERSE[1], UNIVERSE[7]),
                chain(UNIVERSE[2]),
                chain(UNIVERSE[3], UNIVERSE[9]),
            )
            val access = branches.map { it.access }.reduce { l, r -> l.mergeAdd(r) }
            return AccessTree(manager, base, access, ExclusionSet.Empty)
        }

        // The key string encodes the child walk order, so equality here proves the walk
        // order is content-derived, not index-derived.
        assertEquals(
            fwd.factContentKey(multiBranchFact(fwd)),
            rev.factContentKey(multiBranchFact(rev)),
        )
    }

    @Test
    fun `content keys are injective across accessor kinds`() {
        val oneOfEach: List<Accessor> = listOf(
            FieldAccessor("A", "f", "T"),
            ClassStaticAccessor("A"),
            TaintMarkAccessor("A"),
            TypeInfoAccessor("A"),
            ElementAccessor,
            FinalAccessor,
            AnyAccessor,
            ValueAccessor,
            TypeInfoGroupAccessor,
        )
        assertEquals(oneOfEach.size, oneOfEach.map { it.contentKey() }.toSet().size)
    }
}
