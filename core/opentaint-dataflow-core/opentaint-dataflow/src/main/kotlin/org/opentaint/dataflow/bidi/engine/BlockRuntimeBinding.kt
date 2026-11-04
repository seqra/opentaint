package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.AccessPathBase
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
    fun startResult(state: BlockRunState, node: CommonInst, original: PremiseKey, value: Facts)
    fun successors(state: BlockRunState, node: CommonInst, original: PremiseKey, value: Facts)
    fun publish(state: BlockRunState, exit: PortId, publications: List<Publication>)
    fun publishTargets(state: BlockRunState, targets: TargetBatch)
    fun borrowRequests(input: Facts): List<RequestedRow>
    fun borrowRequest(slot: Run1Slot): RequestRowView
    fun commitRequests(state: BlockRunState, temporary: RequestStorage)
    fun staticMarkRequest(initial: InitialAp, mark: TaintMark)
    fun staticTicket(): Long
    fun routeStaticToExit(state: BlockRunState, node: CommonInst, original: PremiseKey, value: Facts)
    fun methodBoundary(state: BlockRunState, node: CommonInst, original: PremiseKey, value: Facts,
                       summary: Boolean)
    fun keepLocalConclusion(exit: PortId, value: Facts): Boolean = true
    /** Query-only normalized C5. Null delegates to the native demand view. */
    fun intersectSummary(exit: PortId, original: PremiseKey, raw: Facts): List<Facts>? = null
    fun prepareExit(exit: PortId, base: AccessPathBase): PreparedExit? = null
    fun deliveryStatistics(): BlockDeliveryStatistics? = null
}

internal data class BlockDeliveryStatistics(val hits: Long, val searches: Long, val visited: Long,
                                          val destinations: Long, val maxWidth: Int)

/** The method actor routes the original boundary stages into their genuine local spans. */
internal interface MethodRootRouting {
    fun start(node: CommonInst, original: InitialAp, value: Facts)
    fun enter(node: CommonInst, original: PremiseKey, value: Facts)
    fun successors(node: CommonInst, original: PremiseKey, value: Facts)
    /** Query-only normalized C5. Null delegates to the native demand view. */
    fun intersectSummary(exit: PortId, original: PremiseKey, raw: Facts): List<Facts>? = null
}
