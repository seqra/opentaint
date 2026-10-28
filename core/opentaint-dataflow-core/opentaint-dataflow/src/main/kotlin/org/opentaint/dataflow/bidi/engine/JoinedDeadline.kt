package org.opentaint.dataflow.bidi.engine

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.CoroutineStart
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.NonCancellable
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.delay
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import kotlin.time.Duration

/** Joined AP/tree loops use the shared cancellation token. An independent
 * watchdog makes the original deadline visible inside those existing checks. */
internal fun <T> withJoinedDeadline(remaining: () -> Duration, onTimeout: () -> Unit, body: () -> T): T {
    val root = SupervisorJob()
    val watchdog = CoroutineScope(Dispatchers.Default + root).launch(start = CoroutineStart.UNDISPATCHED) {
        val left = remaining()
        if (left > Duration.ZERO) delay(left)
        onTimeout()
    }
    try { return body() }
    finally {
        root.cancel()
        runBlocking(NonCancellable) { watchdog.join() }
    }
}
