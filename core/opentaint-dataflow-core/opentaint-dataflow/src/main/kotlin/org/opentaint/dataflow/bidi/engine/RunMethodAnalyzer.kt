package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.ScopedTargetRows
import org.opentaint.dataflow.bidi.store.ScopedRunSummary
import org.opentaint.dataflow.bidi.store.OwnedScope
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.Record
import org.opentaint.dataflow.bidi.store.NormalRuleContributorRow

/** The only scheduled actor for an original method. Block state is owned here. */
class RunMethodAnalyzer(
    key: MethodKey,
    port: RunnerPort<RunMethodAnalyzer>,
    publisher: PublicationSink,
    localFactory: MethodLocalServicesFactory,
    callFactory: MethodCallServicesFactory,
    targetPublisher: TargetPublicationSink,
) : BlockRunState(key, port, publisher, localFactory, callFactory, targetPublisher), RunActor {
    internal var blockRuntime: MethodBlockRuntime? = null
        private set
    private val staticTicketScopes = HashMap<Long, BlockScope>()
    private var localStaticRequests = if (!config.run1) null else LocalStaticInputRequests(ops, mode, key,
        ticket = ::nextStaticTicket,
        interest = { staticBatch.interests += it; requestWork() },
        resume = { link, original, value ->
            checkNotNull(blockRuntime).offerStaticAnswer(link, original as InitialAp, value)
        })
    private var scopedSummaries: List<ScopedRunSummary> = emptyList()
    private var scopedTargets: List<ScopedTargetRows> = emptyList()
    private var scopedOutgoingTargets: List<ScopedTargetRows> = emptyList()
    private var childNormalContributorRows: List<NormalRuleContributorRow> = emptyList()
    private var frozenChildCounters = LongArray(10)
    private var capturedChildCounters = LongArray(10)
    private var joinedMethodCaptured = false
    private var frozenBlockDiagnostics: String? = null
    internal fun blockDiagnostics(): String? = blockRuntime?.diagnosticStatistics() ?: frozenBlockDiagnostics

    init {
        if (port.shared.contexts.blockLayout(key).hasLoops) {
            val runtime = MethodBlockRuntime(this, port, localFactory, callFactory)
            blockRuntime = runtime
            rootRouting = runtime
        }
    }

    private fun children(): Sequence<BlockRunState> = blockRuntime?.states()?.asSequence()
        ?.map { it.second }?.filter { it !== this } ?: emptySequence()
    private fun childCount(slot: Int, count: (BlockRunState) -> Long): Long =
        frozenChildCounters[slot] + children().sumOf(count)

    override val steps get() = super.steps + childCount(0) { it.steps }
    override val edgeDeltas get() = super.edgeDeltas + childCount(1) { it.edgeDeltas }
    override val demandLayerEdges get() = super.demandLayerEdges + childCount(2) { it.demandLayerEdges }
    override val recordCrossings get() = super.recordCrossings + childCount(3) { it.recordCrossings }
    override val triggerSeeds get() = super.triggerSeeds + childCount(4) { it.triggerSeeds }
    override val neutralBatchApplications get() = super.neutralBatchApplications + childCount(5) { it.neutralBatchApplications }
    override val neutralBatchMemberships get() = super.neutralBatchMemberships + childCount(6) { it.neutralBatchMemberships }
    override val neutralBulkStorePackets get() = super.neutralBulkStorePackets + childCount(7) { it.neutralBulkStorePackets }
    override val neutralBulkStoreMemberships get() = super.neutralBulkStoreMemberships + childCount(8) { it.neutralBulkStoreMemberships }
    override val neutralScalarFallbackMemberships get() = super.neutralScalarFallbackMemberships + childCount(9) { it.neutralScalarFallbackMemberships }
    override val hasZeroWork get() = super.hasZeroWork || children().any { it.localHasZeroWork }

    internal fun blockSummaries(): Sequence<ScopedRunSummary> = scopedSummaries.asSequence()
    internal fun blockTargets(): Sequence<ScopedTargetRows> = scopedTargets.asSequence()
    internal fun blockOutgoingTargets(): Sequence<ScopedTargetRows> = scopedOutgoingTargets.asSequence()
    internal fun normalContributorRows(): Sequence<NormalRuleContributorRow> =
        frozenNormalContributorRows.asSequence() + childNormalContributorRows.asSequence()
    internal fun joinedBlockStates(): List<Pair<BlockScope, BlockRunState>> =
        blockRuntime?.states() ?: listOf(BlockScope.ROOT to this)
    internal fun forEachJoinedLocalInput(scope: BlockScope, visit: (LocalLink, Facts) -> Unit) {
        blockRuntime?.forEachLocalInput(scope, visit)
    }

    internal fun detachJoinedLocalInputs(): Map<BlockScope, JoinedLocalInputs> =
        blockRuntime?.detachJoinedLocalInputs().orEmpty()

    internal fun detachJoinedStaticSources(): List<JoinedStaticSource> =
        joinedBlockStates().map { (scope, state) -> state.joinedStaticSource(OwnedScope(key, scope)) }

    internal fun allocateStaticTicket(scope: BlockScope): Long = nextStaticTicket().also {
        check(staticTicketScopes.put(it, scope) == null)
    }

    internal fun requestLocalStaticInput(link: LocalLink, input: Facts, mark: TaintMark) {
        checkNotNull(localStaticRequests).request(link, input as FlowTree, mark)
    }

    override fun requestWork() {
        blockRuntime?.scheduleRoot()
        super.requestWork()
    }

    override fun work(quantum: Int): Boolean = blockRuntime?.work(quantum) ?: super.work(quantum)

    override fun releaseAbstraction() {
        for (state in children()) state.releaseAbstraction()
        super.releaseAbstraction()
    }

    private fun waiting(scope: BlockScope): BlockRunState =
        if (scope == BlockScope.ROOT) this else checkNotNull(blockRuntime).state(scope)

    internal fun addScopedMarkRequests(scope: BlockScope, rows: RequestRows) {
        waiting(scope).addMarkRequests(rows)
    }

    override fun applySummary(part: Subscription, pub: Publication, member: Int) {
        if (part.ref.scope == BlockScope.ROOT) super.applySummary(part, pub, member)
        else waiting(part.ref.scope).applySummary(part, pub, member)
    }
    override fun applyStaticSummary(part: Subscription, pub: Publication, member: Int) {
        if (part.ref.scope == BlockScope.ROOT) super.applyStaticSummary(part, pub, member)
        else waiting(part.ref.scope).applyStaticSummary(part, pub, member)
    }
    override fun applyTarget(part: Subscription, row: TargetSummary, member: Int) {
        if (part.ref.scope == BlockScope.ROOT) super.applyTarget(part, row, member)
        else waiting(part.ref.scope).applyTarget(part, row, member)
    }
    override fun applyStaticTarget(part: Subscription, row: TargetSummary, member: Int) {
        if (part.ref.scope == BlockScope.ROOT) super.applyStaticTarget(part, row, member)
        else waiting(part.ref.scope).applyStaticTarget(part, row, member)
    }
    override fun requestStaticGroups(part: Subscription, marks: org.opentaint.dataflow.bidi.store.RequestMarkSelection) {
        if (part.ref.scope == BlockScope.ROOT) super.requestStaticGroups(part, marks)
        else waiting(part.ref.scope).requestStaticGroups(part, marks)
    }
    override fun applyRecord(part: Subscription, record: Record) {
        if (part.ref.scope == BlockScope.ROOT) super.applyRecord(part, record)
        else waiting(part.ref.scope).applyRecord(part, record)
    }
    override fun applyRecordView(part: Subscription, view: RecordLeafView, nonSubsumable: Boolean) {
        if (part.ref.scope == BlockScope.ROOT) super.applyRecordView(part, view, nonSubsumable)
        else waiting(part.ref.scope).applyRecordView(part, view, nonSubsumable)
    }

    override fun onStaticEffect(effect: StaticOwnerEffect) {
        if (localStaticRequests?.answer(effect) == true) return
        val ticket = when (effect) {
            is StaticOwnerEffect.ReadReady -> effect.id
            is StaticOwnerEffect.PointReady -> effect.id
            is StaticOwnerEffect.WriterInterest -> effect.id
        }
        val scope = staticTicketScopes[ticket]
        if (scope == null) super.onStaticEffect(effect)
        else checkNotNull(blockRuntime).state(scope).onStaticEffect(effect)
    }

    internal override fun captureJoinedExports() {
        if (joinedMethodCaptured) return
        check(!hasLocalWork) { "A method cannot capture unfinished root work" }
        val runtime = blockRuntime
        runtime?.requireIdle()
        joinedMethodCaptured = true // Failed capture cannot be retried during best-effort release.
        val closedChildren = children().toList()
        val completionStatistics = runtime?.completionScalarStatistics()?.toList().orEmpty()
        super.captureJoinedExports()
        for (child in closedChildren) child.captureJoinedExports()
        if (runtime != null) {
            if (context.shared.n2Statistics != null) frozenBlockDiagnostics = runtime.diagnosticStatistics()
            scopedSummaries = runtime.scopedSummaries().toList()
            scopedTargets = runtime.scopedTargets().toList()
            scopedOutgoingTargets = runtime.scopedOutgoingTargets().toList()
            capturedChildCounters = longArrayOf(closedChildren.sumOf { it.steps }, closedChildren.sumOf { it.edgeDeltas },
                closedChildren.sumOf { it.demandLayerEdges }, closedChildren.sumOf { it.recordCrossings },
                closedChildren.sumOf { it.triggerSeeds }, closedChildren.sumOf { it.neutralBatchApplications },
                closedChildren.sumOf { it.neutralBatchMemberships }, closedChildren.sumOf { it.neutralBulkStorePackets },
                closedChildren.sumOf { it.neutralBulkStoreMemberships }, closedChildren.sumOf { it.neutralScalarFallbackMemberships })
        }
        childNormalContributorRows = closedChildren.flatMap { it.frozenNormalContributorRows }
        includeClosedBlockMeasurements(closedChildren, completionStatistics)
    }

    override fun freeze() {
        if (executionReleased) return
        check(!hasLocalWork) { "A method cannot freeze with unfinished root work" }
        blockRuntime?.requireIdle()
        var failure: Throwable? = null
        try { captureJoinedExports() } catch (error: Throwable) { failure = error }
        try { blockRuntime?.freezeChildren() } catch (error: Throwable) {
            if (failure == null) failure = error else if (failure !== error) failure.addSuppressed(error)
        }
        finally {
            blockRuntime = null
            frozenChildCounters = capturedChildCounters
            localStaticRequests?.clear()
            localStaticRequests = null
            staticTicketScopes.clear()
            try { super.freeze() } catch (error: Throwable) {
                if (failure == null) failure = error else if (failure !== error) failure.addSuppressed(error)
            }
        }
        failure?.let { throw it }
    }
}
