package org.opentaint.dataflow.util

import java.lang.management.ManagementFactory
import kotlin.time.Duration

class Cancellation {
    class Cancelled : Exception("Operation cancelled") {
        override fun fillInStackTrace(): Throwable = this
    }

    @Volatile
    private var isActive: Boolean = true

    fun activate() {
        isActive = true
    }

    fun cancel() {
        isActive = false
    }

    fun isActive(): Boolean = isActive

    fun checkpoint() {
        if (isActive) return
        throw Cancelled()
    }

    companion object {
        private val isDebugActive = lazy { getDebuggerAttachment() }

        private fun getDebuggerAttachment() =
            ManagementFactory.getRuntimeMXBean().inputArguments
                .any { it.contains("-agentlib:jdwp") || it.contains("-Xdebug") }

        fun getActiveDuration(duration: Duration) =
            if (isDebugActive.value)
                Duration.INFINITE
            else
                duration
    }
}
