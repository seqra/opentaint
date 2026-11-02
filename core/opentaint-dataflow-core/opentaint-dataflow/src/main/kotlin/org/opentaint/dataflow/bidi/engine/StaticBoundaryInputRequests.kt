package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.PortId
import java.util.ArrayDeque

/** Relay a real point request through the identity inputs of a static exit continuation.
 *
 * Intermediate ROOT_EXIT links pass the same canonical static input without an instruction.
 * The outer link can instead have C.f as its original and C.g as its FLOW image. Its owner
 * handles that relation through the existing local-static or ordinary mark-request path.
 * This query neither supplies a mark nor retains requests or a cross-query seen set.
 */
internal class StaticBoundaryInputRequests(
    private val ops: ApOps,
    private val mode: ApMode,
    private val borrowInputs: (BlockScope, (LocalLink, Facts) -> Unit) -> Unit,
    private val onRoot: (LocalLink, FlowTree, TaintMark) -> Unit,
) {
    private data class Query(val scope: BlockScope, val initial: InitialAp)

    fun request(scope: BlockScope, initial: InitialAp, mark: TaintMark) {
        val ap = ops.manager
        ap.cancellation.checkpoint()
        if (!mode.run1 || mode.direction != Direction.FORWARD || scope.entry != PortId.ROOT_EXIT ||
            initial.base != STATIC || initial.mark !is MarkSlot.Star) return

        val pending = ArrayDeque<Query>()
        val visited = HashSet<Query>()
        fun enqueue(query: Query) {
            if (visited.add(query)) pending.addLast(query)
        }
        enqueue(Query(scope, initial))
        while (pending.isNotEmpty()) {
            ap.cancellation.checkpoint()
            val query = pending.removeFirst()
            borrowInputs(query.scope) { link, actual ->
                ap.cancellation.checkpoint()
                check(link.child == query.scope) { "A static continuation borrows its own registered inputs" }
                if (link.point != PortId.ROOT_EXIT || actual !is FlowTree ||
                    !RuntimeDataDomain.packet(link.original, actual)) return@borrowInputs
                val parentInitial = link.original as? InitialAp ?: return@borrowInputs
                if (parentInitial.mark !is MarkSlot.Star) return@borrowInputs
                val matched = ops.satisfying(actual, query.initial, mode) as? FlowTree ?: return@borrowInputs
                if (link.parent == BlockScope.ROOT) {
                    onRoot(link, matched, mark)
                } else if (link.parent.entry == PortId.ROOT_EXIT && parentInitial == query.initial) {
                    // Only these installed, unchanged inputs are identity continuations.
                    enqueue(Query(link.parent, parentInitial))
                }
            }
        }
    }
}
