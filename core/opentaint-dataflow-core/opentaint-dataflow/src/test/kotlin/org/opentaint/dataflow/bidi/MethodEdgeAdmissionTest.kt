package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.DeltaWorklist
import org.opentaint.dataflow.bidi.engine.EdgeDelta
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.MethodEdgeStore
import kotlin.test.*

/** Completed output membership is independent of pending inputs. */
class MethodEdgeAdmissionTest {
    @Test fun `mixed exact and MAY values admit once and do not replay a covered exact leaf`() {
        MethodAnalysisFixtures().use { f ->
            val store = MethodEdgeStore(f.manager, f.key, f.language, 1)
            val original = f.manager.initial(f.run1Pattern())
            val exact = f.run1Fact(path = listOf(f.field("f"))) as TaintTree
            val may = f.run1Fact(path = listOf(f.field("g")), tail = Tail.ANY) as TaintTree
            val mixed = f.manager.taintTree(exact.base, exact.layer,
                f.manager.taintAlg.mergeAdd(exact.root, may.root), anyTail = Tail.ANY)
            val delta = assertNotNull(store.add(f.inst(1), original, mixed))
            assertEquals(f.ops.leaves(mixed).toSet(), f.ops.leaves(delta).toSet())
            assertNull(store.add(f.inst(1), original, exact))
            assertNull(store.add(f.inst(1), original, mixed))
            assertEquals(f.ops.leaves(mixed).toSet(),
                store.edgesAt(f.inst(1), original).flatMap { f.ops.leaves(it.second) }.toSet())
        }
    }

    @Test fun `FLOW annotation growth emits the whole merged relation then quiesces`() {
        MethodAnalysisFixtures().use { f ->
            val store = MethodEdgeStore(f.manager, f.key, f.language, 1)
            val original = f.manager.initial(f.pattern(tail = Tail.STAR, mark = MarkSlot.STAR))
            val flow = f.ops.startFact(original) as FlowTree
            fun excluding(mark: TaintMark) = f.manager.flowTree(flow.base, flow.layer, flow.exclusion,
                MarkExclusions.of(f.manager.marks, mark), flow.root, flow.tail)
            assertNotNull(store.add(f.inst(1), original, excluding(f.mark("T"))))
            val grown = assertIs<FlowTree>(store.add(f.inst(1), original, excluding(f.mark("U"))))
            assertTrue(grown.markExclusion.isEmpty)
            assertEquals(f.ops.leaves(flow).toSet(), f.ops.leaves(grown).toSet())
            assertNull(store.add(f.inst(1), original, flow))
            assertNull(store.add(f.inst(1), original, excluding(f.mark("T"))))
        }
    }

    @Test fun `equal AP at another statement remains fresh work`() {
        MethodAnalysisFixtures().use { f ->
            val store = MethodEdgeStore(f.manager, f.key, f.language, 1)
            val original = f.manager.initial(f.run1Pattern())
            val fact = f.run1Fact()
            assertNotNull(store.add(f.inst(1), original, fact))
            assertNull(store.add(f.inst(1), original, fact))
            assertNotNull(store.add(f.inst(2), original, fact))
            assertNull(store.add(f.inst(2), original, fact))
        }
    }

    @Test fun `DEMAND and NORMAL AP derivations keep their independent layers`() {
        MethodAnalysisFixtures().use { f ->
            val store = MethodEdgeStore(f.manager, f.key, f.language, 1)
            val original = f.manager.initial(f.pattern(tail = Tail.STAR, mark = MarkSlot.STAR))
            val normal = f.ops.startFact(original)
            val demand = normal.withLayer(Layer.DEMAND)
            assertEquals(Layer.DEMAND, assertNotNull(store.add(f.inst(1), original, demand)).layer)
            assertEquals(Layer.NORMAL, assertNotNull(store.add(f.inst(1), original, normal)).layer)
            assertNull(store.add(f.inst(1), original, demand))
            assertNull(store.add(f.inst(1), original, normal))
        }
    }

    @Test fun `identity self loop stops at durable producer output admission`() {
        MethodAnalysisFixtures().use { f ->
            val store = MethodEdgeStore(f.manager, f.key, f.language, 1)
            val original = f.manager.initial(f.run1Pattern())
            val delta = EdgeDelta(original, f.inst(1), f.run1Fact())
            val work = DeltaWorklist()
            work.add(delta)
            val input = work.removeNext()
            val fresh = assertNotNull(store.add(input.node, input.premise, input.facts))
            work.add(input.copy(facts = fresh))
            val repeated = work.removeNext()
            assertNull(store.add(repeated.node, repeated.premise, repeated.facts))
            assertTrue(work.isEmpty)
            assertEquals(1, store.edgesAt(f.inst(1)).count())
            assertNull(store.add(delta.node, delta.premise, delta.facts), "A later burst cannot replay a completed result")
        }
    }
}
