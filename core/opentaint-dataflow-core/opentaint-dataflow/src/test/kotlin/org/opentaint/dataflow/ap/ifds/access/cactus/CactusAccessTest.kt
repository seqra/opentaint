package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertSame

class CactusAccessTest {
    @Test
    fun `cleaner change re-emits the complete access value`() {
        val markA = TaintMarkAccessor("a")
        val markB = TaintMarkAccessor("b")
        val access = AccessCactus.AccessNode.create(isAbstract = true)
        val cleanedTwice = CactusFinalAccess(
            access,
            AnyFieldCleanerEffects.Empty.add(markA).add(markB),
        )
        val cleanedOnce = CactusFinalAccess(
            access,
            AnyFieldCleanerEffects.Empty.add(markA),
        )

        val (merged, delta) = cleanedTwice.mergeAddDelta(cleanedOnce)

        assertSame(access, merged.access)
        assertEquals(cleanedOnce.cleanerEffects, merged.cleanerEffects)
        assertEquals(merged, assertNotNull(delta))
    }
}
