package org.opentaint.dataflow.util

import java.util.concurrent.CancellationException

class Cancellation {
    class Cancelled : CancellationException("Operation cancelled") {
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
}
