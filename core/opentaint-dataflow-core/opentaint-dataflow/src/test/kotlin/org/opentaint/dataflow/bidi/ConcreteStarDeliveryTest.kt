package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.bidi.store.CallerRef
import kotlin.test.*

class ConcreteStarDeliveryTest {
    @Test fun `concrete STAR publication and descendant input meet in both arrival orders`() {
        val f = EngineShellFixtures()
        val m = f.manager
        val field = m.accessors.index(FieldAccessor("Box", "f", "Box"))
        val p = AccessPathBase.Argument(0)
        val t = MarkSlot.Concrete(m.marks.mark("T"))
        val j = m.initial(p, null, Tail.STAR, ExclusionSet.Empty, t)
        val deep = m.factsOf(PathFact(p, listOf(field), Tail.EXACT, t), ExclusionSet.Empty, Layer.NORMAL)
        val result = m.factsOf(PathFact(AccessPathBase.Return, emptyList(), Tail.STAR, t), ExclusionSet.Empty, Layer.DEMAND)
        val pub = Publication(j, result)
        val sub = Subscription(f.b, CallerRef(f.a, m.zero, Layer.NORMAL, f.inst(f.methodA, 2)), Layer.NORMAL, deep)
        val mode = ApMode(false, Direction.BACKWARD, 1)
        val existingPublications = PublicationIndex(m, f.ops)
        existingPublications.addAll(listOf(pub))
        assertTrue(existingPublications.candidates(sub, mode).any { it.first.premise === j && it.second == 0 })
        val existingInputs = CalleeSubscriptions(f.ops)
        existingInputs.add(sub)
        assertEquals(listOf(sub), existingInputs.candidates(pub, 0, mode).toList())
        assertNotNull(f.ops.satisfying(deep, j, mode))
        val blocked = m.initial(p, null, Tail.STAR, ExclusionSet.of(field), t)
        assertNull(f.ops.satisfying(deep, blocked, mode))
        val wrong = m.factsOf(PathFact(p, listOf(field), Tail.EXACT,
            MarkSlot.Concrete(m.marks.mark("U"))), ExclusionSet.Empty, Layer.NORMAL)
        assertNull(f.ops.satisfying(wrong, j, mode))
    }
}
