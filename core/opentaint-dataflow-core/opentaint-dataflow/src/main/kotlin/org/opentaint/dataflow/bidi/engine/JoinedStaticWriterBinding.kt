package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.OwnedScope
import org.opentaint.dataflow.bidi.store.StaticWriteKeyInterner

/** Source-compatible method-root adapter. Scoped completion uses the same binder directly. */
internal class JoinedStaticWriterBinding(
    ops: ApOps,
    mode: ApMode,
    keys: StaticWriteKeyInterner,
    borrow: (MethodKey, Publication, (Subscription) -> Unit) -> Unit,
    onBound: (MethodKey, InitialAp, Pattern) -> Unit,
    checkpoint: () -> Unit,
) {
    private val binding = OwnedJoinedStaticWriterBinding(ops, mode, keys,
        borrow = { owner, writer, visit ->
            check(owner.local == BlockScope.ROOT) { "The compatibility binder has method-root owners only" }
            borrow(owner.method, writer) { input ->
                check(input.callee == owner.method) { "A writer can bind only its complete callee key" }
                visit(OwnedWriterInput.call(input))
            }
        },
        onBound = { owner, original, result -> onBound(owner.method, original, result) },
        checkpoint = checkpoint)

    fun offer(owner: MethodKey, id: Int) = binding.offer(OwnedScope(owner, BlockScope.ROOT), id)
    fun complete(): Statistics = binding.complete()

    data class Statistics(val writerOffers: Long, val admittedWriters: Long, val processedWriters: Long,
                          val candidateInputs: Long, val duplicateInputs: Long,
                          val matchedInputs: Long, val boundOutputs: Long)
}
