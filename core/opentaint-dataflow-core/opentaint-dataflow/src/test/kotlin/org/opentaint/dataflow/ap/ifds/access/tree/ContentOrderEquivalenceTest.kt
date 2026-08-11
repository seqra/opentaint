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
import org.opentaint.dataflow.ap.ifds.access.util.contentKey
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals

/**
 * The invariant behind deterministic trace fingerprints: everything derived from accessor
 * indices must be a function of accessor CONTENT, never of the order in which threads
 * happened to intern.
 *
 * Accessors are intentionally interned late and in opposite orders. Compact indices may
 * differ, but structural iteration, fact keys, and fact hashes must depend only on content.
 */
class ContentOrderEquivalenceTest {

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

    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private fun managerInterning(order: List<Accessor>): TreeApManager =
        TreeApManager(UnrollStrategy, RefManager(), Cancellation()).also { manager ->
            order.forEach { manager.interner.index(it) }
        }

    private fun multiBranchFact(manager: TreeApManager): AccessTree {
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

    @Test
    fun `late accessors retain canonical order despite opposite indices`() {
        val fwd = managerInterning(UNIVERSE)
        val rev = managerInterning(UNIVERSE.reversed())
        assertNotEquals(
            fwd.interner.index(UNIVERSE.first()),
            rev.interner.index(UNIVERSE.first()),
            "indices must differ for this test to prove content ordering",
        )

        fun rootAccessors(manager: TreeApManager): List<Accessor> =
            multiBranchFact(manager).access.accessors
                ?.map { manager.interner.accessor(it) ?: error("missing accessor $it") }
                .orEmpty()

        val expected = rootAccessors(fwd).sorted()
        assertEquals(expected, rootAccessors(fwd))
        assertEquals(expected, rootAccessors(rev))
    }

    @Test
    fun `fact content key is identical under opposite interning orders`() {
        val fwd = managerInterning(UNIVERSE)
        val rev = managerInterning(UNIVERSE.reversed())

        val moved = UNIVERSE.count { fwd.interner.index(it) != rev.interner.index(it) }
        assertNotEquals(0, moved, "index assignments must differ for this test to prove anything")

        val fwdFact = multiBranchFact(fwd)
        val revFact = multiBranchFact(rev)
        assertEquals(fwd.factContentKey(fwdFact), rev.factContentKey(revFact))
        assertEquals(fwdFact.hashCode(), revFact.hashCode())
    }

    @Test
    fun `initial fact key and hash ignore late accessor indices`() {
        val fwd = managerInterning(UNIVERSE)
        val rev = managerInterning(UNIVERSE.reversed())

        fun fact(manager: TreeApManager) = manager.mostAbstractInitialAp(AccessPathBase.This)
            .prependAccessor(UNIVERSE[3])
            .prependAccessor(UNIVERSE[7])
            .exclude(UNIVERSE[5])
            .exclude(UNIVERSE[4])

        val fwdFact = fact(fwd)
        val revFact = fact(rev)
        assertEquals(fwd.factContentKey(fwdFact), rev.factContentKey(revFact))
        assertEquals(fwdFact.toString(), revFact.toString())
        assertEquals(fwdFact.hashCode(), revFact.hashCode())
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
