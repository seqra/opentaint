package org.opentaint.dataflow.util

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Job
import kotlinx.coroutines.cancelAndJoin
import kotlinx.coroutines.isActive
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class CancellationTest {
    @Test
    fun cancelledCheckpointDoesNotCancelParentCoroutineScope() = runBlocking {
        val parent = Job()
        val scope = CoroutineScope(coroutineContext + parent)
        val cancellation = Cancellation().also { it.cancel() }

        val child = scope.launch {
            cancellation.checkpoint()
        }
        child.join()

        assertTrue(child.isCancelled)
        assertFalse(child.isActive)
        assertTrue(parent.isActive)

        parent.cancelAndJoin()
    }
}
