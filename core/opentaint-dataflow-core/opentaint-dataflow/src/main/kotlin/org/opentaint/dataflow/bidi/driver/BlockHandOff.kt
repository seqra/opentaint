package org.opentaint.dataflow.bidi.driver

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.engine.TargetSummary
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId

/** Only entered scopes contribute rows. A terminal uses its logical exit port.
 * Runtime routing must resolve ROOT_EXIT through the existing directed backend
 * boundary/discovery graph. It is not permission to seed all physical ports. */
data class ScopedTargetRows(
    val method: MethodKey,
    val scope: BlockScope,
    val rows: Collection<TargetSummary>,
    val exit: PortId = PortId.ROOT_EXIT,
)

/** The same AP handoff as the public method boundary, with both control ports
 * reversed. One successful normalized insertion counts as one outgoing row. */
fun projectBlockHandOff(
    ap: ApManager,
    direction: Direction,
    run1: Boolean,
    summaries: Sequence<ScopedRunSummary>,
    targets: Sequence<ScopedTargetRows>,
    demand: DemandStore.Builder,
    counts: MutableMap<MethodKey, Int>,
    onBoundary: (ScopedSummaryKey, Pattern, Pattern) -> Unit = { _, _, _ -> },
) {
    val ops = ApOps(ap)
    for ((producer, store) in summaries) {
        ap.cancellation.checkpoint()
        val next = producer.reversed()
        for ((premise, facts) in store.demandEdges(direction)) {
            ap.cancellation.checkpoint()
            // The same selected STAR/ANY guidance grammar applies at every scope.
            if (direction == Direction.BACKWARD)
                check(premise is InitialAp) { "The backward run has no multi-premise summary (ap.md §9.2)" }
            for (leaf in ops.leaves(facts)) {
                ap.cancellation.checkpoint()
                val entry = guidancePattern(leaf)
                premise.forEachMember { member ->
                    ap.cancellation.checkpoint()
                    val exit = guidancePattern(member.toPattern())
                    onBoundary(producer, exit, entry)
                    if (demand.add(next.method, next.scope, next.exit, DemandPattern(entry, exit)))
                        counts.merge(next.method, 1, Int::plus)
                }
            }
        }
    }
    for (terminal in targets) {
        ap.cancellation.checkpoint()
        val next = ScopedSummaryKey(terminal.method, terminal.scope, terminal.exit).reversed()
        for (row in terminal.rows) {
            ap.cancellation.checkpoint()
            check(row.target == Target.DemandTarget) { "Only outgoing DEMAND Targets guide a later run" }
            row.premise.forEachMember { member ->
                ap.cancellation.checkpoint()
                val exit = if (member.isZero) DemandExit.Zero
                    else DemandExit.Data(guidancePattern(member.toPattern()))
                if (demand.add(next.method, next.scope, next.exit, PairedDemand(DemandEntry.Target, exit)))
                    counts.merge(next.method, 1, Int::plus)
            }
        }
    }
}
