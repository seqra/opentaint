package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.store.*

/** Test-only late-FULL handoff adapter. Mirrors native compaction and keeps
 * exact block ports, DATA, seeds and saved records. Only the selected method
 * root's ZERO/DT origins are absent from this temporary handoff. */
internal fun withoutCertifiedRootTarget(f: DriverFixtures, previous: RunConfig, root: MethodKey): DemandStore {
    check(!previous.run1 && previous.direction == Direction.FORWARD)
    val compactor = HandoffCompactor(f.manager)
    val origins = arrayListOf<HandoffOrigin>()
    for (actor in f.results.last().analyzers) {
        for ((premise,facts) in actor.summaries.demandEdges(previous.direction))
            origins += compactor.summary(HandoffOwner(actor.key),premise,facts)
        for (row in actor.outgoingTargets) if (actor.key != root || !row.premise.isZero)
            origins += compactor.target(HandoffOwner(actor.key),row)
        for ((producer,store) in actor.blockSummaries()) {
            val next = producer.reversed()
            val owner = HandoffOwner(next.method,next.scope,next.exit)
            for ((premise,facts) in store.demandEdges(previous.direction))
                origins += compactor.summary(owner,premise,facts)
        }
        for (terminal in actor.blockOutgoingTargets()) {
            val next = ScopedSummaryKey(terminal.method,terminal.scope,terminal.exit).reversed()
            for (row in terminal.rows) origins += compactor.target(HandoffOwner(next.method,next.scope,next.exit),row)
        }
    }
    val builder = DemandStore.Builder(f.manager)
    for (origin in compactor.select(origins).kept) for (row in origin.rows) {
        val owner = origin.owner
        if (owner.scope == null) builder.add(owner.method,row)
        else builder.add(owner.method,owner.scope,checkNotNull(owner.exit),row)
    }
    return builder.build()
}
