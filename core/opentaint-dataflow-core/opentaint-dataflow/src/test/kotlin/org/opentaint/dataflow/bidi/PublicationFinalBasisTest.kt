package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.CallerRef
import kotlin.test.*

class PublicationFinalBasisTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    @Test fun `one detached batch publishes only its retained MAY basis in each class`() {
        val field = f.field("child")
        val initial = ap.initial(f.pattern(tail = Tail.STAR))
        val mode = ApMode(true, Direction.FORWARD, 1)
        val plainParent = f.fact(tail = Tail.ANY, layer = Layer.DEMAND) as TaintTree
        val plainChild = f.fact(path = listOf(field), tail = Tail.ANY, layer = Layer.DEMAND) as TaintTree
        for (protected in listOf(false, true)) for (parentFirst in listOf(false, true)) {
            val parent = if (protected) plainParent.withProtection(plainParent.root) else plainParent
            val child = if (protected) plainChild.withProtection(plainChild.root) else plainChild
            val index = PublicationIndex(ap, f.ops, flowBacked = true)
            val offered = if (parentFirst) listOf(parent, child) else listOf(child, parent)
            val fresh = index.addAll(offered.map { Publication(initial, it) })
            assertEquals(listOf(parent), fresh.map { it.conclusion })
            val actual = f.fact()
            val ref = CallerRef(f.key("caller"), ap.zero, Layer.NORMAL, f.inst(1))
            val subscription = Subscription(f.method, ref, Layer.NORMAL, actual)
            assertEquals(listOf(parent), index.candidates(subscription, mode).map { it.first.conclusion })
            assertTrue(index.addAll(listOf(Publication(initial, child))).isEmpty())
        }
    }
}
