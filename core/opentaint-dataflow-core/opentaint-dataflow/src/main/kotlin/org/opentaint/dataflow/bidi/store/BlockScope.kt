package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.MethodKey
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId

/** Storage/control identity only. It is not part of a fact, rule or mark key. */
data class BlockScope(val block: BlockId, val entry: PortId) {
    companion object { val ROOT = BlockScope(BlockId(0), PortId.ROOT_ENTRY) }
}

data class OwnedScope(val method: MethodKey, val local: BlockScope)

/** A row keeps both ports. Opposite-direction lookup exchanges their roles. */
data class ScopedSummaryKey(val method: MethodKey, val scope: BlockScope, val exit: PortId) {
    fun reversed(): ScopedSummaryKey = copy(scope = BlockScope(scope.block, exit), exit = scope.entry)
}
