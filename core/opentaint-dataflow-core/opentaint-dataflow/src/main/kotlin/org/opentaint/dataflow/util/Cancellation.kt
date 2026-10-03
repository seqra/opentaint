package org.opentaint.dataflow.util

import java.util.concurrent.CancellationException

class Cancellation private constructor(
    private val parent: Cancellation?,
    private val additionalCondition: (() -> Boolean)?,
) {
    constructor() : this(parent = null, additionalCondition = null)

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

    fun isActive(): Boolean =
        isActive && parent?.isActive() != false && additionalCondition?.invoke() != false

    fun derive(additionalCondition: () -> Boolean): Cancellation =
        Cancellation(parent = this, additionalCondition = additionalCondition)

    fun checkpoint() {
        if (isActive()) return
        throw Cancelled()
    }
}
