package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.ApMode
import org.opentaint.dataflow.bidi.ap.MethodKey

/** Moved existing per-callee accumulators and indexes. No live subscription port. */
internal class JoinedCallerInputs internal constructor(
    private var directory: LinkedHashMap<MethodKey, CalleeSubscriptions>?,
) : AutoCloseable {
    fun visit(callee: MethodKey, writer: Publication, mode: ApMode, visit: (Subscription) -> Unit) {
        checkNotNull(directory) { "Joined caller inputs are closed" }[callee]?.visitJoinedCandidates(writer, mode, visit)
    }
    override fun close() {
        val owned = directory ?: return
        directory = null
        var failure: Throwable? = null
        for (inputs in owned.values) try { inputs.clear() } catch (error: Throwable) {
            if (failure == null) failure = error else if (failure !== error) failure.addSuppressed(error)
        }
        owned.clear()
        failure?.let { throw it }
    }
}
