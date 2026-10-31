package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import kotlin.test.*

/** Prepared AP/algebra controls only; not run during the project campaign. */
class InheritedCoverPruneTest {
    @Test
    fun `a cached folded subtree consumed by inherited cover has no residual`() {
        MethodAnalysisFixtures().use { f ->
            val t = f.mark("T")
            val actual = f.fact(path = listOf(f.field("a"),f.field("b"),f.field("c")),
                mark = MarkSlot.Concrete(t), layer = Layer.DEMAND) as TaintTree
            val inherited = f.manager.taintLeaves(f.manager.markSetOf(t), f.manager.markSetOf(t))
            val alg = f.manager.taintAlg
            val all = alg.foldAll(actual.root, f.cancellation)
            assertTrue(alg.minus(all, inherited).isEmpty)
            val old = alg.subtract(actual.root, null, inherited, at = { it }, below = { it },
                cancellation = f.cancellation)
            assertNull(old)
            assertEquals(4L, actual.root.size)
        }
    }

    @Test
    fun `one uncovered mark prohibits a whole-subtree cut`() {
        MethodAnalysisFixtures().use { f ->
            val t = f.mark("T")
            val u = f.mark("U")
            val actual = f.fact(path = listOf(f.field("a")), mark = MarkSlot.Concrete(u),
                layer = Layer.DEMAND) as TaintTree
            val inherited = f.manager.taintLeaves(f.manager.markSetOf(t), f.manager.markSetOf(t))
            val alg = f.manager.taintAlg
            assertFalse(alg.minus(alg.foldAll(actual.root), inherited).isEmpty)
            assertNotNull(alg.subtract(actual.root, null, inherited, at = { it }, below = { it }))
        }
    }

    @Test
    fun `unprotected MAY storage cannot consume a new protected EXACT dependency`() {
        MethodAnalysisFixtures().use { f ->
            val t = MarkSlot.Concrete(f.mark("T"))
            val base = AccessPathBase.Argument(0)
            val store = TaintGroup(f.manager, f.manager.newInterners().taint)
            val broad = f.fact(base, tail = Tail.ANY, mark = t, layer = Layer.DEMAND) as TaintTree
            val narrow = f.fact(base, listOf(f.field("a"),f.field("b"),f.field("c")),
                Tail.EXACT, t, layer = Layer.DEMAND) as TaintTree
            assertNotNull(store.add(broad))
            assertNull(store.add(narrow))
            val flagged = assertNotNull(store.add(narrow.withProtection(narrow.root)))
            assertNotNull(flagged.nonSubsumable)
            assertEquals(f.ops.leaves(narrow).toList(), f.ops.leaves(flagged).toList())
        }
    }
}
