package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.MethodEdgeStore
import kotlin.test.*

class CanonicalPointAdmissionTest {
    @Test fun `post statement admission delivers every strengthened exclusion header`() {
        for (packed in listOf(false, true)) {
            val f = StoreFixtures()
            val ap = f.manager
            val x = AccessPathBase.Argument(0)
            val t = f.mark("T")
            val u = f.mark("U")
            val a = f.field("a")
            val b = f.field("b")
            val initial = ap.initial(f.pattern(AccessPathBase.Argument(1), mark = MarkSlot.Concrete(t)))
            val store = MethodEdgeStore(ap, f.method, f.lm, 3, flowBacked = packed)
            val both = MarkSet(intArrayOf(t.id, u.id))
            val root = ap.taintTree(x, Layer.NORMAL,
                ap.taintAlg.leafNode(ap.taintLeaves(MarkSet.EMPTY, both)), ExclusionSet.of(intArrayOf(a, b)))
            val childA = f.fact(x, listOf(a), Tail.ANY_TAINT, MarkSlot.Concrete(t)) as TaintTree
            val childB = f.fact(x, listOf(b), Tail.ANY_TAINT, MarkSlot.Concrete(u)) as TaintTree
            val children = childA.withRoot(ap.taintAlg.mergeAdd(childA.root, childB.root, ap.cancellation))
            assertEquals(1, store.addAll(f.inst(1), initial, root).size)
            val fresh = store.addAll(f.inst(1), initial, children)
            val expected = setOf(
                f.pattern(x, tail = Tail.ANY_TAINT, mark = MarkSlot.Concrete(t), exclusion = ExclusionSet.of(b)),
                f.pattern(x, tail = Tail.ANY_TAINT, mark = MarkSlot.Concrete(u), exclusion = ExclusionSet.of(a)))
            assertEquals(expected, fresh.flatMap { f.ops.leaves(it).toList() }.toSet())
            assertEquals(expected, store.edgesAt(f.inst(1), initial).flatMap { f.ops.leaves(it.second) }.toSet())
            assertTrue(store.addAll(f.inst(1), initial, children).isEmpty())
            assertTrue(store.edgesAt(f.inst(2), initial).none(), "S output must not be stored at its successor")
        }
    }
}
