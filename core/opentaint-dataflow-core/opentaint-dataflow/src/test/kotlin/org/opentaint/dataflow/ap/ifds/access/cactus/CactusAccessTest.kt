package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyFieldMarkExclusions
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull

class CactusAccessTest {
    @Test
    fun `cleaner change re-emits the complete access value`() {
        val markA = TaintMarkAccessor("a")
        val markB = TaintMarkAccessor("b")
        val access = AccessCactus.AccessNode.create(isAbstract = true)
        val cleanedTwice = access.withAnyFieldMarkExclusions(
            AnyFieldMarkExclusions.Empty
                .add(CactusMarkInterner.index(markA))
                .add(CactusMarkInterner.index(markB)),
        )
        val cleanedOnce = access.withAnyFieldMarkExclusions(
            AnyFieldMarkExclusions.Empty.add(CactusMarkInterner.index(markA)),
        )

        val (merged, delta) = cleanedTwice.mergeAddDelta(cleanedOnce)

        assertEquals(
            access,
            merged.withAnyFieldMarkExclusions(AnyFieldMarkExclusions.Empty),
        )
        assertEquals(cleanedOnce.anyFieldMarkExclusions, merged.anyFieldMarkExclusions)
        assertEquals(merged, assertNotNull(delta))
    }
}
