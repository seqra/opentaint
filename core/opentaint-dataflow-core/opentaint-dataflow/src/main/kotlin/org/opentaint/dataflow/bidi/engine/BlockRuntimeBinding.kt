package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId
import org.opentaint.ir.api.common.cfg.CommonInst

/** Explicit owner services for one local entry. No callback selects an active block. */
internal interface BlockRuntimeBinding {
    val scope: BlockScope
    val context: RunMethodContext
    val points: PointDirectory<CommonInst>
    val bodyWork: BodyWorkStatistics?
    val sourceHits: SourceHitStore?
    val sinkSeeds: LinkedHashSet<org.opentaint.dataflow.bidi.driver.Seed>
    val demand: ScopeDemandView?
    val terminalExit: PortId get() = if (context.config.direction == Direction.FORWARD)
        PortId.ROOT_EXIT else PortId.ROOT_ENTRY
    fun schedule()
    fun start(state: BlockRunState, original: InitialAp, value: Facts)
    fun successors(state: BlockRunState, node: CommonInst, original: PremiseKey, value: Facts)
    fun publish(state: BlockRunState, exit: PortId, publications: List<Publication>)
    fun publishTargets(state: BlockRunState, targets: TargetBatch)
    fun borrowRequests(input: Facts): List<RequestedRow>
    fun borrowRequest(slot: Run1Slot): RequestRowView
    fun commitRequests(state: BlockRunState, temporary: RequestStorage)
    fun staticTicket(): Long
    fun routeStaticToExit(state: BlockRunState, node: CommonInst, original: PremiseKey, value: Facts)
    fun methodBoundary(state: BlockRunState, node: CommonInst, original: PremiseKey, value: Facts,
                       summary: Boolean)
    fun deliveryStatistics(): BlockDeliveryStatistics? = null
}

internal data class BlockDeliveryStatistics(val hits: Long, val searches: Long, val visited: Long,
                                          val destinations: Long, val maxWidth: Int)

/** The real method entry/exit stays at the root; physical work descends through local links. */
internal interface MethodRootRouting {
    fun enter(node: CommonInst, original: PremiseKey, value: Facts)
    fun successors(node: CommonInst, original: PremiseKey, value: Facts)
}
