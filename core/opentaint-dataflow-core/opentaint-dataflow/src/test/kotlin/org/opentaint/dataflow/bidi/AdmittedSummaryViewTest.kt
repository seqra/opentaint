package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.RunSummaryStore
import kotlin.test.*

class AdmittedSummaryViewTest {
    @Test fun `one admitted relation supplies both borrowed and outgoing views`() {
        val f = StoreFixtures()
        val store = RunSummaryStore(f.manager)
        val key = f.manager.initial(f.pattern())
        val piece = f.fact(layer = Layer.DEMAND)
        assertNotNull(store.addAdmitted(key, piece))
        assertNull(store.addAdmitted(key, piece), "Outgoing guidance is a view, not another owner")
        assertEquals(listOf(piece), store.borrow(key).toList())
        assertEquals(listOf(key to piece), store.demandEdges(Direction.FORWARD).toList())
    }
}
