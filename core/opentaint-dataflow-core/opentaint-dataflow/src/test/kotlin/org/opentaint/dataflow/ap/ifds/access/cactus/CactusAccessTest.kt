package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.add
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull

class CactusAccessTest {
    @Test
    fun `cleaner change re-emits the complete access value`() {
        val markA = TaintMarkAccessor("a")
        val markB = TaintMarkAccessor("b")
        val interner = AccessorInterner()
        val access = AccessCactus.AccessNode.create(isAbstract = true)
        val cleanedTwice = access.withAnyFieldAccessorExclusions(
            null
                .add(interner.index(markA))
                .add(interner.index(markB)),
        )
        val cleanedOnce = access.withAnyFieldAccessorExclusions(
            null.add(interner.index(markA)),
        )

        val (merged, delta) = cleanedTwice.mergeAddDelta(cleanedOnce)

        assertEquals(
            access,
            merged.withAnyFieldAccessorExclusions(null),
        )
        assertEquals(cleanedOnce.deepAccessorExclusion, merged.deepAccessorExclusion)
        assertEquals(merged, assertNotNull(delta))
    }
}
