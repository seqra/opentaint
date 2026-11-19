package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.store.*

internal fun withoutCertifiedRootTarget(f: DriverFixtures, previous: RunConfig, root: MethodKey): DemandStore {
    check(!previous.run1 && previous.direction == Direction.FORWARD)
    return rebuildHandoff(f, previous.direction) { origin ->
        origin.owner.method == root && origin.owner.scope == null &&
            origin.rows == listOf(PairedDemand(DemandEntry.Target, DemandExit.Zero))
    }
}

/** Rebuild a late FULL handoff from the joined run, with an explicit test cut. */
internal fun rebuildHandoff(
    f: DriverFixtures,
    direction: Direction,
    omit: (HandoffOrigin) -> Boolean,
): DemandStore {
    val compactor = HandoffCompactor(f.manager)
    val origins = arrayListOf<HandoffOrigin>()
    for (actor in f.results.last().analyzers) {
        val method = HandoffOwner(actor.key)
        for ((premise, facts) in actor.summaries.demandEdges(direction))
            origins += compactor.summary(method, premise, facts)
        for (row in actor.outgoingTargets)
            origins += compactor.target(method, row)
        for ((producer, store) in actor.blockSummaries()) {
            val next = producer.reversed()
            val owner = HandoffOwner(next.method, next.scope, next.exit)
            for ((premise, facts) in store.demandEdges(direction))
                origins += compactor.summary(owner, premise, facts)
        }
        for (terminal in actor.blockOutgoingTargets()) {
            val next = ScopedSummaryKey(terminal.method, terminal.scope, terminal.exit).reversed()
            val owner = HandoffOwner(next.method, next.scope, next.exit)
            for (row in terminal.rows) origins += compactor.target(owner, row)
        }
    }
    val builder = DemandStore.Builder(f.manager)
    for (origin in compactor.select(origins.filterNot(omit)).kept) for (row in origin.rows) {
        val owner = origin.owner
        if (owner.scope == null) builder.add(owner.method, row)
        else builder.add(owner.method, owner.scope, checkNotNull(owner.exit), row)
    }
    return builder.build()
}
