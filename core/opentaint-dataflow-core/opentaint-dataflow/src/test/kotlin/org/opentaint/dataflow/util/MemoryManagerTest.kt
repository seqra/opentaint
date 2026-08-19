package org.opentaint.dataflow.util

import java.lang.management.ManagementFactory
import kotlin.test.Test
import kotlin.test.assertEquals

class MemoryManagerTest {
    @Test
    fun `each analysis run gets independent memory pressure state`() {
        val manager = MemoryManager(RefManager(), memoryThreshold = 0.9) {}
        val memory = ManagementFactory.getMemoryMXBean()
        val firstRun = manager.GCNotificationListener(memory)
        val secondRun = manager.GCNotificationListener(memory)

        firstRun.memoryManagerState.set(MemoryManager.State.GcAfterCleanup)

        assertEquals(MemoryManager.State.Normal, secondRun.memoryManagerState.get())
    }
}
