package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.Collections
import org.opentaint.dataflow.graph.PortId

/** Mutable transfer state. The original method actor owns its scheduling and lifetime. */
open class BlockRunState internal constructor(
    val key: MethodKey,
    port: RunnerPort<RunMethodAnalyzer>,
    publisher: PublicationSink,
    localFactory: MethodLocalServicesFactory,
    callFactory: MethodCallServicesFactory,
    targetPublisher: TargetPublicationSink,
    internal val binding: BlockRuntimeBinding? = null,
) : SummaryApplier {
    private var port: RunnerPort<RunMethodAnalyzer>? = port
    private var runContext: RunMethodContext? = binding?.context ?: RunMethodContext(key, port.forms, port.config, port.shared)
    val scope: BlockScope get() = binding?.scope ?: BlockScope.ROOT
    internal val isRootScope: Boolean get() = binding == null
    internal var rootRouting: MethodRootRouting? = null
    internal val runnerPort: RunnerPort<RunMethodAnalyzer> get() = checkNotNull(port) { "The method is frozen" }
    internal val context: RunMethodContext get() = checkNotNull(runContext) { "The method is frozen" }
    internal val config: RunConfig get() = context.config
    internal val forms: DirectedForms get() = context.forms
    internal val ap: ApManager = port.shared.ap
    internal val ops: ApOps = port.shared.ops
    internal val mode: ApMode = port.config.mode
    internal val forward: Boolean = port.config.direction == Direction.FORWARD
    private val limit = port.config.fieldLimit
    private var bodyWork = if (binding != null) binding.bodyWork else context.bodyWorkStatistics()
    internal val sharedBodyWork: BodyWorkStatistics? get() = bodyWork
    internal var bodyWorkSnapshot: BodyWorkSnapshot? = null; private set
    /** The run manager may call this only after all runner jobs have joined.
     * It copies numeric diagnostics; it does not export an incomplete run store. */
    internal fun stoppedBodyWorkSnapshot(): BodyWorkSnapshot? = bodyWorkSnapshot ?: bodyWork?.snapshot()
    internal val diagnosticCandidateOffers: Long get() =
        bodyWorkSnapshot?.candidatePackets ?: bodyWork?.candidatePackets ?: 0L

    private var edgeStore: ScopedEdgeStore<CommonInst>? = if (binding != null) ScopedEdgeStore(ap, binding.points, limit,
        flowBacked = mode.run1 && mode.markMode == MarkMode.FULL,
        collectStatistics = port.shared.n2Statistics != null) else MethodEdgeStore(ap, key, port.shared.language, limit,
        flowBacked = mode.run1 && mode.markMode == MarkMode.FULL,
        collectStatistics = port.shared.n2Statistics != null)
    private var initialStore: InitialFactStore? = InitialFactStore()
    val edges: ScopedEdgeStore<CommonInst> get() = checkNotNull(edgeStore) { "The method edges were released" }
    val initials: InitialFactStore get() = checkNotNull(initialStore) { "The initial facts were released" }
    val summaries = RunSummaryStore(ap, flowBacked = true)
    internal val normalRuleContributors = NormalRuleContributors(ap,
        port.shared.normalRuleContributors.snapshot(), key, scope, mode)
    internal var frozenNormalContributorRows: List<NormalRuleContributorRow> = emptyList()
        private set
    internal val portSummaries = PortSummaryStores(ap, flowBacked = true)
    private var localPublications = LinkedHashMap<PortId, MutableList<Publication>>()
    val sourceHits: SourceHitStore? = if (binding != null) binding.sourceHits else if (forward) null else SourceHitStore()
    val staticGuidanceSeeds = StaticGuidanceSeedStore(ap, ops, port.shared.staticGuidanceInterner)
    private val staticWriteCandidates = if (mode.run1)
        KilledStaticWriteStore(key, ap, ops, port.shared.staticWriteKeyInterner) else null

    /** Joined guidance completion only; raw observed rows still support ordinary call binding.
     * This also works after actor freeze for existing synthetic handoff fixtures. */
    fun freezeStaticWriteCandidates(): FrozenStaticWrites {
        check(mode.run1) { "Static-write candidate guidance exists only for run-1" }
        val admitted = if (isRootScope) summaries.all()
            else portSummaries.entries().asSequence().flatMap { it.second.all() }
        return checkNotNull(staticWriteCandidates).freeze(admitted, staticGuidanceSeeds.frozenRows())
    }
    internal fun joinedStaticSource(owner: OwnedScope): JoinedStaticSource {
        check(mode.run1)
        return JoinedStaticSource(owner, summaries.takeIf { isRootScope },
            portSummaries.takeUnless { isRootScope }, outgoingTargets, staticGuidanceSeeds,
            checkNotNull(staticWriteCandidates))
    }

    private val checkRun2StaticAnchors = config.index == 2
    private var temporary = RequestStorage()
    private var temporarySinceNanos = 0L
    private val staticSupplyProfile = if (config.run1 && config.direction == Direction.FORWARD &&
        mode.markMode == MarkMode.FULL) SupplyProfile.CANONICAL_RUN1_FULL else SupplyProfile.ORDERED_REFERENCE
    internal var staticBatch = StaticBatch(staticSupplyProfile, ap.cancellation, context.shared.n2Statistics); private set
    private var pointResumes = if (config.run1) Run1PointResume(this) else null
    private data class PointWork(val premise: PremiseKey, val facts: Facts,
                                 val site: ResumeSite, val state: CallResumeState?)
    private data class RuleItem(val premise: PremiseKey, val facts: Facts)
    private var resumeQueue = java.util.ArrayDeque<PointWork>()
    private val operationOwner = FormOwner()
    internal var abstraction: Run1Abstraction? = if (config.run1) Run1Abstraction(
        ops,
        answer = ::addInitial,
        borrowRequests = { input -> binding?.borrowRequests(input) ?: runnerPort.summaryStorage(key).borrowMatchingRequests(input) },
        collectRequests = ::collectRequests,
        statistics = context.shared.requestBatchStatistics,
        policyStatistics = context.shared.abstractionStatistics,
        owner = key,
    ) else null
        private set
    internal open fun releaseAbstraction() {
        abstraction?.release(); abstraction = null
        if (!temporary.isEmpty) {
            context.shared.abstractionStatistics?.temporaryChanged(-temporary.dynamicRows.toLong(), -temporary.dynamicMembers)
            temporary = RequestStorage()
        }
        temporarySinceNanos = 0L
    }
    internal fun unchangedStaticInitial(premise: PremiseKey): InitialAp? =
        null // The selected design has no inherited static request suppression.

    private var publicationSink: PublicationSink? = publisher
    private var local: MethodLocalServices? = localFactory.create(this)
    private var calls: MethodCallServices? = callFactory.create(this)
    internal val localServices: MethodLocalServices get() = checkNotNull(local) { "The local services were released" }
    private val callServices: MethodCallServices get() = checkNotNull(calls) { "The call services were released" }
    private var formApplier: FormApplier<PremiseKey, Facts>? = FormApplier(EngineAlgebra(this))
    internal val applier get() = checkNotNull(formApplier) { "The form applier was released" }
    private var worklist = DeltaWorklist(flowFirst = mode.run1 && mode.markMode == MarkMode.FULL,
        batchManager = ap.takeIf { mode.run1 && mode.markMode == MarkMode.FULL })
    private var pending = ArrayList<Publication>()
    private var targetPublicationSink: TargetPublicationSink? = targetPublisher
    private var pendingTargets = ArrayList<TargetSummary>()
    private val rawTargetRows = LinkedHashSet<TargetSummary>()
    val targets: Set<TargetSummary> get() = Collections.unmodifiableSet(rawTargetRows)
    private val outgoingTargetRows = LinkedHashSet<TargetSummary>()
    val outgoingTargets: Set<TargetSummary> get() = Collections.unmodifiableSet(outgoingTargetRows)
    val sinkSeeds = binding?.sinkSeeds ?: LinkedHashSet<org.opentaint.dataflow.bidi.driver.Seed>()
    /** Report observation only. Blocks share their method owner's current-run set. */
    internal val reachedSinkReportIds = binding?.reachedSinkReportIds ?: LinkedHashSet<ReportId>()

    internal fun emitTarget(premise: PremiseKey, target: Target) {
        if (!RuntimeDataDomain.premise(premise)) return
        if (!forward && target is Target.NormalTarget) return
        premise.forEachMember { check(!it.isFlow) { "Target needs a concrete or ZERO origin" } }
        if (target is Target.NormalTarget && (if (isRootScope) config.normalTargets.contains(key, premise, target.id)
                else config.normalTargets.contains(key, scope, premise, target.id))) return
        val row = TargetSummary(premise, target)
        if (!rawTargetRows.add(row)) return
        if (target is Target.NormalTarget || config.run1 ||
            (binding?.demand?.acceptsTarget(binding.terminalExit, premise, config.admissionPolicy)
                ?: checkNotNull(config.demand).acceptsTarget(key, premise, config.admissionPolicy))) {
            pendingTargets += row
            if (target == Target.DemandTarget) outgoingTargetRows += row
            requestWork()
        }
    }

    private var localSteps: Long = 0
    open val steps: Long get() = localSteps
    open val hasZeroWork: Boolean get() = worklist.hasZeroWork
    private var localEdgeDeltas: Long = 0
    open val edgeDeltas: Long get() = localEdgeDeltas
    private var localDemandLayerEdges: Long = 0
    open val demandLayerEdges: Long get() = localDemandLayerEdges
    var nonZeroInitial: Boolean = false; private set
    private var localRecordCrossings: Long = 0
    open val recordCrossings: Long get() = localRecordCrossings
    private var localTriggerSeeds: Long = 0
    open val triggerSeeds: Long get() = localTriggerSeeds
    private var localNeutralBatchApplications: Long = 0
    open val neutralBatchApplications: Long get() = localNeutralBatchApplications
    private var localNeutralBatchMemberships: Long = 0
    open val neutralBatchMemberships: Long get() = localNeutralBatchMemberships
    private var localNeutralBulkStorePackets: Long = 0
    open val neutralBulkStorePackets: Long get() = localNeutralBulkStorePackets
    private var localNeutralBulkStoreMemberships: Long = 0
    open val neutralBulkStoreMemberships: Long get() = localNeutralBulkStoreMemberships
    private var localNeutralScalarFallbackMemberships: Long = 0
    open val neutralScalarFallbackMemberships: Long get() = localNeutralScalarFallbackMemberships
    var cfgDeliveryHits: Long = 0; private set
    var cfgDeliverySearches: Long = 0; private set
    var cfgDeliveryVisitedNodes: Long = 0; private set
    var cfgDeliveryDestinations: Long = 0; private set
    var cfgDeliveryMaxWidth: Int = 0; private set
    /** Scalar gauges copied before release. No premise, fact or actor is retained. */
    var scalarIdentityStatistics: ScalarIdentityStatistics? = null; private set

    private var initialized = false

    /** Called only by the registered actor's owner; use the ordinary publication path. */
    private fun initialize() {
        if (initialized) return
        initialized = true
        // Static reads and effects start only at their reached operation.
    }

    fun addRootZero() {
        if (config.run1) addInitial(ap.zero)
        else for (initial in emitRestrictedInitials(config, ops, key, Reach.NORMAL)) addInitial(initial)
    }

    fun addLink(ref: CallerRef, linkLayer: Layer, added: Facts) {
        if (!RuntimeDataDomain.packet(ref.premise, added)) return
        check(config.run1) { "Raw call inputs are for run-1 only" }
        checkPremise(ref.premise)
        ap.cancellation.checkpoint()
        initialize()
        check(added.base !is AccessPathBase.CleanerTemporary) { "A field-action temporary cannot enter an added link" }
        check(linkLayer == added.layer) { "The link layer must be the added fact's layer" }
        context.shared.abstractionStatistics?.arrival()
        // Diagnostic input presence; this is not selected outgoing demand or a retained-group count.
        if (added.layer == Layer.DEMAND && !sawDemandInput) { sawDemandInput = true; localDemandLayerEdges++ }
        checkNotNull(abstraction).emit(ref, added)
    }

    private var sawDemandInput = false

    fun addMarkRequest(premise: InitialAp, mark: TaintMark) {
        check(config.run1) { "Requests exist only in run 1" }
        localServices.addMarkRequest(premise, mark)
    }

    fun addMarkRequests(premise: InitialAp, marks: RequestMarkSet) {
        check(config.run1) { "Requests exist only in run 1" }
        localServices.addMarkRequests(premise, marks)
    }

    fun addMarkRequests(rows: RequestRows) {
        check(config.run1) { "Requests exist only in run 1" }
        for ((slot, marks) in rows) { ap.cancellation.checkpoint(); collectRequests(slot, marks) }
    }

    internal fun collectRequests(slot: Run1Slot, offered: RequestMarkSelection) {
        initialize()
        check(config.run1) { "Requests exist only in run 1" }
        val statistics = context.shared.abstractionStatistics
        val counts = statistics?.let { RequestAdmissionCounts() }
        val beforeRows = temporary.dynamicRows
        val beforeMembers = temporary.dynamicMembers
        try {
            val fresh = offered.minus(binding?.borrowRequest(slot) ?: runnerPort.summaryStorage(key).borrowRequest(slot), counts, ap.cancellation::checkpoint)
            if (fresh.isEmpty) return
            val delta = temporary.addAll(slot, fresh, counts, ap.cancellation::checkpoint)
            if (!delta.isEmpty && temporarySinceNanos == 0L && context.shared.requestBatchStatistics != null)
                temporarySinceNanos = System.nanoTime()
            requestWork() // also schedules request-only actors; producers never read P
        } finally {
            if (counts != null) {
                counts.freshTemporaryMembers = temporary.dynamicMembers - beforeMembers
                statistics?.temporaryChanged((temporary.dynamicRows - beforeRows).toLong(), counts.freshTemporaryMembers)
                statistics?.requestOffer(counts)
            }
        }
    }

    internal fun addInitial(initial: InitialAp) = addInitial(AdmittedInitial(initial, Layer.NORMAL))

    internal fun addInitial(admitted: AdmittedInitial) {
        val initial = admitted.initial
        check(initial.tail != Tail.ANY) { "An owned initial cannot have an ANY tail" }
        if (!RuntimeDataDomain.initial(initial)) return
        ap.cancellation.checkpoint()
        initialize()
        if (config.run1) {
            validateRun1Initial(initial, limit)
            check(initial.base != STATIC) { "Run-1 static descriptors resume at an operation, not method entry" }
        }
        check(forward || initial.tail != Tail.ANY_TAINT) { "A backward run has no must premise" }
        val intrinsic = ops.startFact(initial, mode)
        val start = forceRun1Layer(initial, intrinsic.withLayer(intrinsic.layer or (admitted.layer == Layer.DEMAND)))
        val fresh = initials.add(AdmittedInitial(initial, start.layer))
        context.shared.abstractionStatistics?.initial(fresh)
        if (!fresh) return
        if (!initial.isZero) nonZeroInitial = true
        if (binding != null) {
            binding.start(this, initial, start)
            return
        }
        for (node in forms.startNodes(key, zero = initial.isZero)) {
            ap.cancellation.checkpoint()
            rootRouting?.start(node, initial, start) ?: startAt(initial, node, start)
        }
    }

    internal fun collect(premise: PremiseKey, input: Facts, sink: ResultSink): ApOut {
        return object : ApOut {
            override fun result(f: Facts) {
                if (!RuntimeDataDomain.packet(premise, input) || !RuntimeDataDomain.packet(premise, f)) return
                val runtime = forceRun1Layer(premise, f)
                if (config.run1) ops.run1Cover(runtime) { value -> value.membershipPackets(ap).forEach { sink(premise, it) } }
                else runtime.membershipPackets(ap).forEach { sink(premise, it) }
            }
            override fun markRequest(mark: TaintMark): Unit = raiseMark(premise, input, mark)
        }
    }

    internal fun raiseMark(premise: PremiseKey, input: Facts, mark: TaintMark) {
        if (!RuntimeDataDomain.packet(premise, input)) return
        check(config.run1) { "Requests exist only in run 1" }
        check(input is FlowTree && premise is InitialAp) { "A request needs a FLOW input premise" }
        check(premise.base != STATIC) { "A static-origin interest needs an exact operation input" }
        addMarkRequest(premise, mark)
    }

    internal fun operation(node: CommonInst, ordinal: Int = 0): OperationId =
        OperationId(FormKey(operationOwner, key.method, key, node), ordinal)

    internal fun forceRun1Layer(premise: PremiseKey, value: Facts): Facts {
        if (!config.run1) return value
        return run1Layer(premise, ops.runtimeFact(value, mode))
    }

    /** FULL uses the ordinary AP layer. GROUP projection and the independent
     * run-1 static approximation keep their DEMAND policy. */
    private fun run1Layer(premise: PremiseKey, value: Facts): Facts {
        return if ((value is TaintTree && mode.markMode == MarkMode.GROUP) || value.base == STATIC ||
            Run1StaticService.hasStaticMember(premise)) value.withLayer(Layer.DEMAND) else value
    }

    internal fun collect(at: OperationInput, sink: ResultSink): ApOut {
        return object : ApOut {
            override fun result(f: Facts) {
                if (!RuntimeDataDomain.packet(at.premise, at.facts) || !RuntimeDataDomain.packet(at.premise, f)) return
                val value = forceRun1Layer(at.premise, f)
                if (config.run1) ops.run1Cover(value) { covered -> covered.membershipPackets(ap).forEach { sink(at.premise, it) } }
                else value.membershipPackets(ap).forEach { sink(at.premise, it) }
            }
            override fun markRequest(mark: TaintMark) = needGroups(at, mark)
        }
    }

    /** Only for the immediate callback from this actor's ops.applyEdge run1Policy.
     * That policy already projected and covered each result with this AP manager. */
    internal fun collectAfterRun1Policy(at: OperationInput, sink: ResultSink): ApOut {
        return object : ApOut {
            override fun result(f: Facts) {
                if (!RuntimeDataDomain.packet(at.premise, at.facts) || !RuntimeDataDomain.packet(at.premise, f)) return
                val value = if (config.run1) run1Layer(at.premise, f) else f
                if (config.run1) ops.run1Cover(value) { covered -> covered.membershipPackets(ap).forEach { sink(at.premise, it) } }
                else value.membershipPackets(ap).forEach { sink(at.premise, it) }
            }
            override fun markRequest(mark: TaintMark) = needGroups(at, mark)
        }
    }

    internal fun needGroups(at: OperationInput, mark: TaintMark) {
        if (!RuntimeDataDomain.packet(at.premise, at.facts)) return
        if (!config.run1) return
        val original = at.premise as? InitialAp ?: return
        if (at.facts !is FlowTree || original.mark !is MarkSlot.Star) return
        if (dropsStaticField(original)) return
        val atom = ap.marks.runtimeAtom(mark, mode.markMode)
        if (original.base == STATIC) {
            checkNotNull(pointResumes).request(at, MarkSet.of(atom))
            binding?.staticMarkRequest(original, atom)
        } else addMarkRequest(original, atom)
    }

    /** FULL block requests share one immutable image and one raw suffix address. */
    internal fun needGroups(at: OperationInput, marks: MarkSet) {
        if (!RuntimeDataDomain.packet(at.premise, at.facts)) return
        if (!config.run1 || marks.isEmpty) return
        val original = at.premise as? InitialAp ?: return
        if (at.facts !is FlowTree || original.mark !is MarkSlot.Star || dropsStaticField(original)) return
        check(mode.markMode == MarkMode.FULL)
        if (original.base == STATIC) {
            checkNotNull(pointResumes).request(at, marks)
            for (id in marks.ids) binding?.staticMarkRequest(original, TaintMark(id))
        } else addMarkRequests(original, RequestMarkSet.fromIds(marks.ids))
    }

    internal fun reachedOperations(summary: StatementSummary, at: OperationInput) {
        if (!RuntimeDataDomain.packet(at.premise, at.facts)) return
        if (config.run1) checkNotNull(pointResumes).reached(summary, at)
    }

    internal fun emitOperationResult(at: OperationInput, operation: StaticOperation.Write?, value: Facts, sink: ResultSink) {
        if (!RuntimeDataDomain.packet(at.premise, at.facts) || !RuntimeDataDomain.packet(at.premise, value)) return
        if (dropsStaticPremise(at.premise)) return
        val admitted = withoutDisabledStaticFields(value) ?: return
        val runtime = forceRun1Layer(at.premise, admitted)
        if (config.run1 && runtime.base == STATIC) {
            val boundary = at.site as? ResumeSite.BoundaryInput
            if (operation != null) {
                boundedSummaryResult(at.premise, runtime) { premise, bounded ->
                    if (boundary != null && !boundary.atStart &&
                        context.isEnd(boundary.operation.form.statement) &&
                        !context.isExceptionalExit(boundary.operation.form.statement)) {
                        // The next exit-rule continuation can kill this executed
                        // write before the final boundary result is available.
                        checkNotNull(staticWriteCandidates).observe(premise, bounded)
                    }
                    // A real write becomes globally visible at the producer,
                    // independently of its later exit rules and summary.
                    checkNotNull(pointResumes).localWrite(premise, bounded)
                    if (boundary != null && !boundary.atStart) sink(premise, bounded)
                    else routeBoundedRun1StaticToExit(at.site.operation.form.statement, premise, bounded)
                }
            } else if (boundary != null && !boundary.atStart) {
                // This value already belongs to an exit-rule pipeline. Finish
                // its remaining rules; never schedule NormalExit again.
                sink(at.premise, runtime)
            }
            return
        }

        sink(at.premise, runtime)
    }

    open fun onStaticEffect(effect: StaticOwnerEffect) {
        check(config.run1 && effect.owner == key)
        checkNotNull(pointResumes).onEffect(effect)
    }

    internal fun staticFacts(slice: RegionGroups): Facts = checkNotNull(runnerPort.staticService).facts(slice.region, slice.groups)
    internal fun staticSlices(facts: Facts): List<RegionGroups> = checkNotNull(runnerPort.staticService).slices(facts)
    internal fun staticCallInterest(part: Subscription, result: StaticCallResult, member: Int) {
        if (!dropsStaticField(result.premise.member(member)))
            checkNotNull(pointResumes).callInterest(part, result, member)
    }
    internal fun staticCallSupply(part: Subscription, result: StaticCallResult, member: Int, supply: RegionGroups) =
        callServices.staticSupply(part, result, member, supply)

    /** These published run-1 originals have already received their canonical pool input. */
    internal fun hasKnownStaticGroupInput(premise: PremiseKey): Boolean =
        config.run1 && premise is InitialAp &&
            premise.base == STATIC && premise.mark is MarkSlot.Concrete &&
            premise.exclusion == ExclusionSet.Empty &&
            ((premise.pathData.size == 2 && premise.tail == Tail.STAR) ||
                (premise.pathData.size == 1 && premise.tail == Tail.EXACT))

    internal fun knownStaticInput(initial: InitialAp): Facts {
        check(hasKnownStaticGroupInput(initial))
        return ops.startFact(initial, mode)
    }

    private fun boundedStaticSummaryOut(premise: PremiseKey, emit: (Facts) -> Unit): ApOut = object : ApOut {
        override fun result(f: Facts) {
            if (f is TaintTree) {
                // Static effects leave the ordinary call suffix early. Apply
                // the same field limit that suffix would apply to its result.
                ops.limit(forceRun1Layer(premise, f), limit, collect(premise, f) { _, bounded -> emit(bounded) })
            }
        }
        override fun markRequest(mark: TaintMark) = Unit // summary application is not rule execution
    }

    internal fun composeStaticSummaryWithActualInput(initial: InitialAp, value: Facts, actual: Facts,
                                                    emit: (Facts) -> Unit) {
        checkPremise(initial)
        val matched = ops.satisfying(actual, initial, mode) ?: return
        ops.applySummary(matched, initial, value, mode, boundedStaticSummaryOut(initial, emit))
    }

    /** Apply a complete static tuple on this owner after releasing the service lock. */
    internal fun composeStaticSummary(premise: PremiseKey, value: Facts, inputs: List<RegionGroups>, emit: (Facts) -> Unit) {
        checkPremise(premise)
        when (premise) {
            is InitialAp -> if (premise.isZero) { if (value is TaintTree) emit(value.withLayer(Layer.DEMAND)) }
                else if (inputs.size == 1) {
                    composeStaticSummaryWithActualInput(premise, value, staticFacts(inputs.single()), emit)
                }
            is PremiseSet -> if (inputs.size == premise.size && value is TaintTree) {
                val parts = inputs.mapIndexed { i, slice ->
                    ap.cancellation.checkpoint()
                    val initial = premise.member(i)
                    val matched = ops.satisfying(staticFacts(slice), initial, mode) ?: return
                    matched to initial
                }
                ops.applyCombination(parts, value, mode, boundedStaticSummaryOut(premise, emit))
            }
        }
    }

    internal fun installPoint(premise: PremiseKey, value: Facts, site: ResumeSite, state: CallResumeState? = null) {
        if (!RuntimeDataDomain.packet(premise, value)) return
        check(config.run1)
        checkPremise(premise)
        if (dropsStaticPremise(premise)) return
        val admitted = withoutDisabledStaticFields(value) ?: return
        premise.forEachMember { validateRun1Initial(it, limit) }
        val runtime = forceRun1Layer(premise, admitted)
        checkKinds(premise, runtime)
        nonZeroInitial = nonZeroInitial || !premise.isZero
        resumeQueue.addLast(PointWork(premise, runtime, site, state))
        requestWork()
    }

    internal fun cut(point: Cut, premise: PremiseKey, facts: Facts, sink: ResultSink) {
        if (!RuntimeDataDomain.packet(premise, facts)) return
        runnerPort.onCut?.invoke(point, facts)
        val checkedSink: ResultSink = if (!checkRun2StaticAnchors) sink else { pr, bounded ->
            validateStaticFullAnchors(bounded)
            sink(pr, bounded)
        }
        val out = collect(premise, facts, checkedSink)
        if (config.run1) ops.run1Cover(facts) { ops.limit(it, limit, out) }
        else ops.limit(facts, limit, out)
    }

    /** Current result headers stay unchanged. Only query/seed admission requires
     * EXACT/ANY with empty E; other bounded field facts can retain MUST/E. */
    private fun validateStaticFullAnchors(facts: Facts) {
        if (facts !is TaintTree || facts.base != STATIC) return
        for (leaf in ops.leaves(facts)) validateRun2StaticFullAnchor(ap, leaf)
    }

    private val hasPendingAbstractionWork: Boolean get() =
        !temporary.isEmpty || !staticBatch.isEmpty || resumeQueue.isNotEmpty()

    internal val hasLocalWork: Boolean get() = !worklist.isEmpty || pending.isNotEmpty() ||
        localPublications.isNotEmpty() || pendingTargets.isNotEmpty() || hasPendingAbstractionWork
    internal val localHasZeroWork: Boolean get() = worklist.hasZeroWork
    internal val localHasFlowWork: Boolean get() = worklist.hasFlowWork

    private fun commitRequests() {
        if (!config.run1 || temporary.isEmpty) return
        if (temporarySinceNanos != 0L)
            context.shared.requestBatchStatistics?.serviceDelay(System.nanoTime() - temporarySinceNanos)
        if (binding != null) binding.commitRequests(this, temporary) else runnerPort.summaryStorage(key).commit(temporary)
        context.shared.abstractionStatistics?.temporaryChanged(-temporary.dynamicRows.toLong(), -temporary.dynamicMembers)
        temporary = RequestStorage() // replace only after synchronous commit and secured sends
        temporarySinceNanos = 0L
    }

    open fun work(quantum: Int): Boolean = workLocal(quantum)

    internal fun workLocal(quantum: Int): Boolean {
        require(quantum > 0) { "The work quantum must be positive" }
        checkNotNull(port) { "The method is frozen" }
        val zeroAtStart = worklist.hasZeroWork
        var processed = 0
        while (true) {
            ap.cancellation.checkpoint()
            while (resumeQueue.isNotEmpty()) {
                if (processed >= quantum) return false
                processed++
                val resume = resumeQueue.removeFirst()
                when (val site = resume.site) {
                    is ResumeSite.StatementInput -> runStatement(EdgeDelta(resume.premise, site.operation.form.statement, resume.facts))
                    is ResumeSite.BoundaryInput -> if (site.atStart) startAt(resume.premise, site.operation.form.statement, resume.facts)
                        else endAt(resume.premise, site.operation.form.statement, resume.facts,
                            summary = !context.isExceptionalExit(site.operation.form.statement))
                    is ResumeSite.ReadOutput -> installPoint(resume.premise, resume.facts, site.input, resume.state)
                    is ResumeSite.CallStageInput, is ResumeSite.CleanerInput -> callServices.resumePoint(resume.premise, resume.facts, site, resume.state)
                }
            }
            while (!worklist.isEmpty) {
                // Keep the zero phase separate. A quantum yield retains P without publishing it;
                // only the method fact-queue-empty boundary commits request memberships.
                if (worklist.hasZeroWork != zeroAtStart) return false
                if (processed >= quantum) {
                    return false
                }
                if (mode.run1 && mode.markMode == MarkMode.FULL)
                    processed += processPending(worklist.removeNextBatch(), quantum - processed)
                else {
                    processed++
                    process(worklist.removeNext())
                }
            }
            flushPublications()
            ap.cancellation.checkpoint()
            if (!worklist.isEmpty || pending.isNotEmpty() || localPublications.isNotEmpty() || pendingTargets.isNotEmpty()) continue
            commitRequests()
            if (config.run1 && !staticBatch.isEmpty) {
                val committed = staticBatch
                val effects = checkNotNull(runnerPort.staticService) { "Run-1 needs its static service" }.commit(committed)
                staticBatch = StaticBatch(staticSupplyProfile, ap.cancellation, context.shared.n2Statistics)
                for (effect in effects) check(runnerPort.sendStatic(effect)) { "Static effect delivery was rejected" }
            }
            ap.cancellation.checkpoint()
            // Retain the counted Work reservation through P commit/replacement and sends.
            if (worklist.isEmpty && pending.isEmpty() && localPublications.isEmpty() && pendingTargets.isEmpty() && !hasPendingAbstractionWork) return true
        }
    }

    private fun process(item: EdgeDelta) {
        if (!RuntimeDataDomain.packet(item.premise, item.facts)) return
        ap.cancellation.checkpoint()
        localSteps++
        bodyWork?.processed(context.shared.language.getInstIndex(item.node), item.premise, item.facts)
        runnerPort.onProcess?.invoke(key, item)
        if (config.run1 && item.facts.base == STATIC && context.isEnd(item.node))
            completeMethodBoundary(item.premise, item.node, item.facts, summary = true)
        else if (context.callAt(item.node) != null) callServices.process(item) else runStatement(item)
    }

    /** A batch can cross only a certified plain statement. Keep a remainder
     * counted as work before any successor, yield or request/static barrier. */
    private fun processPending(work: PendingWork, budget: Int): Int {
        if (work is PendingWork.Scalar) {
            process(work.delta)
            return 1
        }
        work as PendingWork.MarkedBatch
        val node = work.node
        var used = 0
        val plainPoint = binding == null && rootRouting == null && context.callAt(node) == null && !context.isEnd(node) &&
            !context.isExceptionalExit(node) && runnerPort.onProcess == null && runnerPort.onCut == null &&
            !dropsStaticField(work.batch.initialShape)
        if (plainPoint) forms.withStatement(key, node) { summary ->
            if (!NeutralRelationBatch.certifies(summary)) return@withStatement
            val chunk = work.batch.take(budget)
            used = chunk.size
            worklist.addBatch(node, work.batch)
            localSteps += used
            localNeutralBatchApplications++
            localNeutralBatchMemberships += used
            check(chunk.applyPacked(ops, summary, mode,
                emit = { shape, facts, marks -> emitPackedAfter(node, shape, facts, marks) },
                untouched = { shape, facts, marks ->
                    NeutralRelationBatch.decodePacked(ap, shape, facts, marks) { premise, value ->
                        emitUnchanged(EdgeDelta(premise, node, value))
                    }
                }))
        }
        if (used != 0) return used
        val (premise, facts) = work.batch.removeFirst()
        worklist.addBatch(node, work.batch)
        process(EdgeDelta(premise, node, facts))
        return 1
    }

    private fun emitPackedAfter(node: CommonInst, shape: InitialAp, facts: TaintTree, marks: MarkSet) {
        if (!RuntimeDataDomain.packet(shape, facts)) return
        val offered = NeutralRelationBatch.toDiagonal(ap, shape, facts, marks)
        if (offered == null) {
            // Classify once, then use the exact decoder for an unsupported
            // tail or partial-protection cell. No scalar tree is built first.
            localNeutralScalarFallbackMemberships += marks.size
            NeutralRelationBatch.decodePacked(ap, shape, facts, marks) { premise, value -> emitAfter(premise, node, value) }
            return
        }
        check(!context.isEnd(node) && !context.isExceptionalExit(node))
        val fresh = edges.addDiagonal(node, offered)
        if (fresh == null) {
            // Decode once at the producer, before successor fan-out.
            localNeutralScalarFallbackMemberships += marks.size
            NeutralRelationBatch.decodePacked(ap, shape, facts, marks) { premise, value ->
                completeOutput(premise, node, value)
            }
        } else for (delta in fresh) {
            ap.cancellation.checkpoint()
            localNeutralBulkStorePackets++
            localNeutralBulkStoreMemberships += delta.marks.size
            localEdgeDeltas += delta.marks.size
            if (delta.layer == Layer.DEMAND) localDemandLayerEdges += delta.marks.size
            context.forEachSuccessor(node) { successor ->
                context.forEachDeliveryTarget(successor, delta.base) { target ->
                    // Each queued destination owns its mutable remaining-mark wrapper.
                    worklist.addBatch(target, checkNotNull(NeutralRelationBatch.fromDiagonal(ap, delta)))
                    requestWork()
                }
            }
        }
    }

    private fun runStatement(item: EdgeDelta) {
        forms.withStatement(key, item.node) { summary ->
            applier.statement(summary, item.premise, item.facts,
                Place(item.node, config.run1, sources = true, site = ResumeSite.StatementInput(operation(item.node))),
                sink = { premise, result ->
                    cut(Cut.STATEMENT, premise, result) { pr, facts -> emitAfter(pr, item.node, facts) }
                }, untouched = { _, _ -> emitUnchanged(item) })
        }
    }

    internal fun emitAfter(premise: PremiseKey, node: CommonInst, value: Facts) {
        if (!RuntimeDataDomain.packet(premise, value)) return
        checkPremise(premise)
        if (config.run1 && value.base == STATIC && !context.isEnd(node)) return
        if (config.run1) ops.run1Cover(forceRun1Layer(premise, value)) { emitCovered(premise, node, it) }
        else emitCovered(premise, node, value)
    }

    private fun emitCovered(premise: PremiseKey, node: CommonInst, facts: Facts) {
        when {
            context.isEnd(node) -> completeMethodBoundary(premise, node, facts, summary = true)
            context.isExceptionalExit(node) -> completeMethodBoundary(premise, node, facts, summary = false)
            else -> completeOutput(premise, node, facts)
        }
    }

    private fun completeMethodBoundary(premise: PremiseKey, node: CommonInst, facts: Facts, summary: Boolean) {
        if (binding != null) binding.methodBoundary(this, node, premise, facts, summary)
        else endAt(premise, node, facts, summary)
    }

    internal fun emitUnchanged(item: EdgeDelta) {
        if (!RuntimeDataDomain.packet(item.premise, item.facts)) return
        checkPremise(item.premise)
        if (config.run1 && item.facts.base == STATIC && !context.isEnd(item.node)) return
        emitCovered(item.premise, item.node, item.facts)
    }

    /** One durable result row per producer. Identity output uses this gate too. */
    private fun completeOutput(premise: PremiseKey, node: CommonInst, facts: Facts) {
        for (fresh in admitOutputs(node, premise, facts)) {
            // Complete fan-out while the current Work reservation is held.
            if (binding != null) binding.successors(this, node, premise, fresh)
            else if (rootRouting != null) checkNotNull(rootRouting).successors(node, premise, fresh)
            else context.forEachSuccessor(node) { deliverAt(it, premise, fresh) }
        }
    }

    private fun admitOutputs(node: CommonInst, premise: PremiseKey, facts: Facts): List<Facts> {
        if (!RuntimeDataDomain.packet(premise, facts)) return emptyList()
        checkKinds(premise, facts)
        return edges.addAll(node, premise, facts).onEach { fresh ->
            bodyWork?.fresh(context.shared.language.getInstIndex(node), premise, fresh)
            localEdgeDeltas++
            if (fresh.layer == Layer.DEMAND) localDemandLayerEdges++
        }
    }

    private fun deliverAt(start: CommonInst, premise: PremiseKey, facts: Facts) {
        rootRouting?.let { it.enter(start, premise, facts); return }
        context.forEachDeliveryTarget(start, facts.base) { enqueueInput(it, premise, facts) }
    }

    internal fun enqueueInput(node: CommonInst, premise: PremiseKey, facts: Facts) {
        if (!RuntimeDataDomain.packet(premise, facts)) return
        checkKinds(premise, facts)
        worklist.add(EdgeDelta(premise, node, facts))
        requestWork()
    }

    internal fun checkPremise(premise: PremiseKey) {
        check(!config.run1 || premise is InitialAp) { "Run-1 executable edges have one original premise" }
    }

    internal fun checkKinds(premise: PremiseKey, facts: Facts) {
        checkPremise(premise)
        check((facts is FlowTree) == premise.isFlow) { "K6: the conclusion kind follows its premise" }
        check(premise !is PremiseSet || facts is TaintTree) { "A multi-premise edge must be TAINT" }
        if (config.run1) when (facts) {
            is FlowTree -> check(facts.exclusion == ExclusionSet.Empty) { "Run-1 FLOW has Empty field E" }
            is TaintTree -> check(facts.exclusion == ExclusionSet.Empty) { "Run-1 TAINT has Empty field E" }
            is Reach -> Unit
        }
    }

    internal open fun requestWork() {
        if (binding != null) binding.schedule() else runnerPort.enqueue(this as RunMethodAnalyzer)
    }

    internal fun nextStaticTicket(): Long = binding?.staticTicket() ?: ++lastStaticTicket
    private var lastStaticTicket = 0L

    private inner class RuleWorklist(
        private val rules: RuleStatement,
        private val node: CommonInst,
        private val point: Cut,
    ) {
        private val items = LinkedHashMap<Pair<PremiseKey, Facts>, RuleItem>()
        private val add: ResultSink = { premise, facts ->
            cut(point, premise, facts) { pr, result ->
                val key = pr to result
                val old = items[key]
                val merged = if (old == null) result else ap.mergeAddDelta(old.facts, result).first
                items[key] = RuleItem(pr, merged)
            }
        }

        fun input(premise: PremiseKey, facts: Facts) {
            applier.statement(rules.summary, premise, facts, Place(node, config.run1, sources = true,
                site = ResumeSite.BoundaryInput(operation(node), point == Cut.ENTRY_RULES)), sink = add)
        }

        fun drain(after: (PremiseKey, Facts, Triggers) -> Unit = { _, _, _ -> }) {
            for (item in items.values) {
                ap.cancellation.checkpoint()
                val premise = item.premise; val facts = item.facts
                val triggers = localServices.checkSinksAt(premise, node, facts, rules.sinks,
                    OperationInput(ResumeSite.BoundaryInput(operation(node), point == Cut.ENTRY_RULES), premise, facts))
                after(premise, facts, triggers)
            }
        }

        fun forEachResult(visit: (PremiseKey, Facts) -> Unit) {
            for (item in items.values) { visit(item.premise, item.facts) }
        }
    }

    internal fun startAt(premise: PremiseKey, node: CommonInst, start: Facts,
                         deliver: (PremiseKey, Facts) -> Unit = { pr, value ->
                             binding?.startResult(this, node, pr, value) ?: deliverAt(node, pr, value) }) {
        if (!RuntimeDataDomain.packet(premise, start)) return
        forms.withStartRules(key, node) { rules ->
            val work = RuleWorklist(rules, node,
                if (forward) Cut.ENTRY_RULES else Cut.EXIT_RULES)
            work.input(premise, start)
            if (!forward && premise.isZero) localServices.fireSinkSeeds(node) { seed -> work.input(ap.zero, seed) }
            work.drain()
            work.forEachResult { pr, facts ->
                ap.cancellation.checkpoint()
                if (config.run1 && facts.base == STATIC) return@forEachResult
                deliver(pr, facts)
            }
        }
    }

    internal fun endAt(premise: PremiseKey, node: CommonInst, facts: Facts, summary: Boolean) {
        if (!RuntimeDataDomain.packet(premise, facts)) return
        if (config.run1 && summary) checkNotNull(staticWriteCandidates).observe(premise, facts)
        forms.withEndRules(key, node) { exit ->
            val work = RuleWorklist(exit.rules, node, if (forward) Cut.EXIT_RULES else Cut.ENTRY_RULES)
            work.input(premise, facts)
            work.drain { pr, value, triggers ->
                if (!summary) {
                    // Exceptional rules and observations still run, but normal
                    // summary adjustment and killed-write guidance do not.
                    for (fresh in admitOutputs(node, pr, value))
                        if (binding != null) retainBlockSummary(PortId(-4), pr, fresh)
                    return@drain
                }
                if (config.run1) checkNotNull(staticWriteCandidates).observe(pr, value)
                // Local span rows include the real boundary rules. G2 and entry-mark
                // metadata use the complete method origin after parent binding.
                val result = if (isRootScope) finishMethodData(ops, mode, pr, value, exit, triggers.parts) else value
                result?.let { completed ->
                    boundedSummaryResult(pr, completed) { boundedPremise, bounded ->
                        for (fresh in admitOutputs(node, boundedPremise, bounded))
                            retainSummary(boundedPremise, fresh, binding?.terminalExit ?: PortId.ROOT_EXIT)
                    }
                }
            }
        }
    }

    /** Complete method-origin metadata only. The real boundary rules already ran in a leaf. */
    internal fun finishBoundMethodBoundary(premise: PremiseKey, node: CommonInst, value: Facts, summary: Boolean) {
        if (!summary) return
        if (config.run1) checkNotNull(staticWriteCandidates).observe(premise, value)
        forms.withEndRules(key, node) { exit ->
            adjustMethodExitMetadata(premise, value, exit)?.let { summaryDelta(premise, it) }
        }
    }

    internal fun adjustMethodExitMetadata(premise: PremiseKey, value: Facts, exit: ExitRules): Facts? =
        finishMethodData(ops, mode, premise, value, exit)

    /** Query adapter for the same ordered metadata, with no rule actions or joins. */
    internal fun adjustObservedMethodExit(premise: PremiseKey, value: Facts): Facts? {
        var result: Facts? = null
        val node = if (forward) context.normalExit else context.shared.interpreter.entryNode(key)
        forms.withEndRules(key, node) { exit -> result = adjustMethodExitMetadata(premise, value, exit) }
        return result
    }

    internal fun dropsStaticField(fact: PathFact): Boolean =
        config.disableRun1Statics && fact.base == STATIC && fact.path.size >= 2

    internal fun dropsStaticField(initial: InitialAp): Boolean =
        config.disableRun1Statics && initial.base == STATIC && initial.pathData.size >= 2

    private fun dropsStaticPremise(premise: PremiseKey): Boolean = config.disableRun1Statics &&
        (0 until premise.size).any { dropsStaticField(premise.member(it)) }

    /** The diagnostic gate runs before summary/index/publication or writer effects.
     * A packed STATIC tree can also contain exact global class markers. Keep them. */
    private fun withoutDisabledStaticFields(value: Facts): Facts? {
        if (!config.disableRun1Statics || value.base != STATIC) return value
        var kept: Facts? = null
        for (leaf in ops.leaves(value)) {
            if (leaf.fact.path.size != 1 || leaf.fact.tail != Tail.EXACT) continue
            val exact = ap.factsOf(leaf.fact, leaf.exclusion, value.layer)
            kept = kept?.let { ap.mergeAddDelta(it, exact).first } ?: exact
        }
        return kept
    }

    /** A call result supplies its computed mark, but is not a new local writer. */
    internal fun routeStaticResultToExit(node: CommonInst, premise: PremiseKey, value: Facts) {
        check(config.run1 && value.base == STATIC) { "Static exit routing needs a run-1 static result" }
        boundedSummaryResult(premise, value) { pr, bounded ->
            checkNotNull(pointResumes).computedGroups(pr, bounded)
            routeBoundedRun1StaticToExit(node, pr, bounded)
        }
    }

    private fun routeBoundedRun1StaticToExit(node: CommonInst, premise: PremiseKey, bounded: Facts) {
        check(config.run1 && bounded.base == STATIC)
        for (fresh in admitOutputs(node, premise, bounded)) {
            if (binding != null) binding.routeStaticToExit(this, node, premise, fresh)
            else enqueueInput(context.normalExit, premise, fresh)
        }
    }

    internal fun summaryDelta(premise: PremiseKey, value: Facts) =
        boundedSummaryResult(premise, value, ::retainSummary)

    private fun boundedSummaryResult(premise: PremiseKey, value: Facts, sink: ResultSink) {
        checkPremise(premise)
        if (dropsStaticPremise(premise)) return
        val admitted = withoutDisabledStaticFields(value) ?: return
        val runtime = if (config.run1) forceRun1Layer(premise, admitted).let {
            // A nonstatic FLOW original does not itself force a static result
            // to DEMAND. Preserve the explicit static boundary assignment.
            if (it.base == STATIC) it.withLayer(Layer.DEMAND) else it
        } else admitted
        if (config.run1) ops.run1Cover(runtime) { covered ->
            // Static producer routing bypasses the ordinary successor cut.
            // Preserve the same bounded AP value at that boundary.
            ops.limit(covered, limit, collect(premise, covered, sink))
        }
        else {
            // Native/summary producers can reach this boundary without a new
            // successor cut. Keep the producer's existing bound and annotations.
            if (checkRun2StaticAnchors) validateStaticFullAnchors(admitted)
            sink(premise, admitted)
        }
    }

    internal fun retainBlockSummary(exit: PortId, premise: PremiseKey, facts: Facts) {
        boundedSummaryResult(premise, facts) { pr, value -> retainSummary(pr, value, exit) }
    }

    private fun retainSummary(rawPremise: PremiseKey, rawFacts: Facts, exit: PortId = PortId.ROOT_EXIT) {
        if (!RuntimeDataDomain.packet(rawPremise, rawFacts)) return
        val preparedExit = binding?.prepareExit(exit, rawFacts.base)
        if (preparedExit === PreparedExit.DeadData ||
            preparedExit == null && binding?.keepLocalConclusion(exit, rawFacts) == false) return
        val normalized = normalizeFlowSummary(ap, rawPremise, rawFacts)
        val premise = normalized.premise
        val facts = normalized.facts
        val trace = LoopPipelineTrace.enabled(config.index, key)
        if (trace) LoopPipelineTrace.record(config.index, key, "c5-normalized") {
            catalog(ap)
            text("scope", scope.toString())
            number("exit", exit.ordinal)
            this.premise("rawP", rawPremise)
            this.facts("rawF", rawFacts)
            this.premise("P", premise)
            this.facts("F", facts)
        }
        bodyWork?.candidate(premise, facts, internalBlock = !isRootScope)
        assertCanonicalFlowSummary(premise, facts)
        // DEMAND does not imply ANY: paired C5 can preserve a correlated STAR.
        checkKinds(premise, facts)
        if (isRootScope && !context.shared.interpreter.isSummaryBase(facts.base)) return
        // Existing computed summary supplies are independent of local write
        // effects. Pending fixed-mark joins own their scalar payload without
        // retaining a static/static method summary.
        if (config.run1 && facts.base == STATIC) checkNotNull(pointResumes).computedGroups(premise, facts)
        if (isRootScope && erasesRun1StaticSummary(premise, facts)) {
            staticGuidanceSeeds.add(premise, facts)
            return
        }
        val admitted = if (config.run1) listOf(facts) else
            binding?.intersectSummary(exit, premise, facts)
                ?: rootRouting?.intersectSummary(exit, premise, facts)
                ?: binding?.demand?.intersect(exit, premise, facts, config.admissionPolicy)
                ?: checkNotNull(config.demand).intersect(key, premise, facts, config.admissionPolicy)
        for (piece in admitted) {
            ap.cancellation.checkpoint()
            checkKinds(premise, piece)
            if (trace) LoopPipelineTrace.record(config.index, key, "c5-admitted") {
                catalog(ap)
                text("scope", scope.toString())
                number("exit", exit.ordinal)
                this.premise("P", premise)
                this.facts("F", piece)
            }
            val store = if (isRootScope) summaries else portSummaries.at(exit)
            for (delta in store.addAdmittedAll(premise, piece)) {
                localEdgeDeltas++
                if (delta.layer == Layer.DEMAND) localDemandLayerEdges++
                if (isRootScope) pending += Publication(premise, delta)
                else localPublications.getOrPut(exit, ::ArrayList).add(Publication(premise, delta))
            }
        }
        if (pending.isNotEmpty() || localPublications.isNotEmpty()) requestWork()
    }

    internal fun erasesRun1StaticSummary(premise: PremiseKey, facts: Facts): Boolean =
        config.run1 && facts.base == STATIC && !premise.isZero &&
            (0 until premise.size).all { premise.member(it).base == STATIC }

    private fun flushPublications() {
        if (pendingTargets.isNotEmpty()) {
            val detachedTargets = pendingTargets
            pendingTargets = ArrayList()
            try {
                if (binding != null) binding.publishTargets(this, Collections.unmodifiableList(detachedTargets))
                else checkNotNull(targetPublicationSink).publishTargets(key, Collections.unmodifiableList(detachedTargets))
            } catch (error: Throwable) {
                pendingTargets.addAll(0, detachedTargets)
                throw error
            }
        }
        if (localPublications.isNotEmpty()) {
            val detachedLocal = localPublications.toList()
            localPublications.clear()
            for ((exit, rows) in detachedLocal) checkNotNull(binding).publish(this, exit, Collections.unmodifiableList(rows))
        }
        if (pending.isEmpty()) return
        val detached = pending
        pending = ArrayList()
        val batch: List<Publication> = Collections.unmodifiableList(detached)
        try {
            checkNotNull(publicationSink).publish(key, batch)
        } catch (error: Throwable) {
            pending.addAll(0, detached)
            throw error
        }
    }

    override open fun applyTarget(part: Subscription, row: TargetSummary, member: Int): Unit =
        callServices.applyTarget(part, row, member)
    override open fun applyStaticTarget(part: Subscription, row: TargetSummary, member: Int): Unit =
        callServices.applyStaticTarget(part, row, member)
    override open fun applySummary(part: Subscription, pub: Publication, member: Int): Unit =
        callServices.applySummary(part, pub, member)
    override open fun applyStaticSummary(part: Subscription, pub: Publication, member: Int): Unit =
        callServices.applyStaticSummary(part, pub, member)
    override open fun requestStaticGroups(part: Subscription, marks: RequestMarkSelection) {
        check(config.run1 && part.ref.premise.isFlow && part.added is FlowTree)
        val at = OperationInput(ResumeSite.CallStageInput(operation(part.ref.call, part.ref.stageOrdinal)),
            part.ref.premise, part.added, CallResumeState(part.ref.callerLayer))
        val cursor = marks.cursor()
        while (!cursor.isComplete) {
            ap.cancellation.checkpoint()
            cursor.step(256) { needGroups(at, it) }
        }
    }
    override open fun applyRecord(part: Subscription, record: Record): Unit = callServices.applyRecord(part, record)
    override open fun applyRecordView(part: Subscription, view: RecordLeafView, nonSubsumable: Boolean): Unit =
        callServices.applyRecordView(part, view, nonSubsumable)
    internal fun countRecordCrossing() { localRecordCrossings++ }
    internal fun countTriggerSeed() { localTriggerSeeds++ }

    /** Copy closed local-store gauges only. No child state remains in the method result. */
    internal fun includeClosedBlockMeasurements(
        blocks: Collection<BlockRunState>,
        completionStatistics: Collection<ScalarIdentityStatistics> = emptyList(),
    ) {
        cfgDeliveryHits += blocks.sumOf { it.cfgDeliveryHits }
        cfgDeliverySearches += blocks.sumOf { it.cfgDeliverySearches }
        cfgDeliveryVisitedNodes += blocks.sumOf { it.cfgDeliveryVisitedNodes }
        cfgDeliveryDestinations += blocks.sumOf { it.cfgDeliveryDestinations }
        cfgDeliveryMaxWidth = maxOf(cfgDeliveryMaxWidth, blocks.maxOfOrNull { it.cfgDeliveryMaxWidth } ?: 0)
        val snapshots = listOfNotNull(scalarIdentityStatistics) + blocks.mapNotNull { it.scalarIdentityStatistics } +
            completionStatistics
        if (snapshots.isEmpty()) return
        val reasons = LinkedHashMap<String, Long>()
        for (snapshot in snapshots) for ((reason, count) in snapshot.fallbackReasons)
            reasons[reason] = (reasons[reason] ?: 0L) + count
        scalarIdentityStatistics = ScalarIdentityStatistics(
            compactPoints = snapshots.sumOf { it.compactPoints },
            compactNormal = snapshots.sumOf { it.compactNormal },
            compactDemand = snapshots.sumOf { it.compactDemand },
            compactFlow = snapshots.sumOf { it.compactFlow },
            compactTaint = snapshots.sumOf { it.compactTaint },
            protectedNormal = snapshots.sumOf { it.protectedNormal },
            protectedDemand = snapshots.sumOf { it.protectedDemand },
            fullPoints = snapshots.sumOf { it.fullPoints },
            promotedPoints = snapshots.sumOf { it.promotedPoints },
            firstFullPoints = snapshots.sumOf { it.firstFullPoints },
            bitWords = snapshots.sumOf { it.bitWords },
            fullArrayCapacity = snapshots.sumOf { it.fullArrayCapacity },
            fallbackReasons = java.util.Collections.unmodifiableMap(reasons),
        )
    }

    private var joinedCaptured = false
    internal var executionReleased = false; private set

    internal open fun captureJoinedExports() {
        check(!executionReleased) { "Method execution was released" }
        if (joinedCaptured) return
        check(worklist.isEmpty && pending.isEmpty() && localPublications.isEmpty() && pendingTargets.isEmpty() && !hasPendingAbstractionWork) {
            "A method cannot capture unfinished work"
        }
        joinedCaptured = true // A failed capture must still be releasable without a second freezeRows call.
        frozenNormalContributorRows = normalRuleContributors.freezeRows()
        if (binding == null) context.delivery.let {
            cfgDeliveryHits = it.hits; cfgDeliverySearches = it.searches
            cfgDeliveryVisitedNodes = it.visitedNodes; cfgDeliveryDestinations = it.destinations
            cfgDeliveryMaxWidth = it.maxWidth
        } else binding.deliveryStatistics()?.let {
            cfgDeliveryHits = it.hits; cfgDeliverySearches = it.searches
            cfgDeliveryVisitedNodes = it.visited; cfgDeliveryDestinations = it.destinations
            cfgDeliveryMaxWidth = it.maxWidth
        }
        scalarIdentityStatistics = edgeStore?.scalarStatisticsSnapshot()
        if (isRootScope) bodyWorkSnapshot = bodyWork?.snapshot()
    }

    open fun freeze() {
        if (executionReleased) return
        check(worklist.isEmpty && pending.isEmpty() && localPublications.isEmpty() && pendingTargets.isEmpty() && !hasPendingAbstractionWork) {
            "A method cannot freeze with unfinished work"
        }
        var failure: Throwable? = null
        try { captureJoinedExports() } catch (error: Throwable) { failure = error }
        fun release(action: () -> Unit) {
            try { action() }
            catch (error: Throwable) {
                val first = failure
                if (first == null) failure = error
                else if (error !== first) first.addSuppressed(error)
            }
        }
        try {
            release { releaseAbstraction() }
            release { localServices.freeze() }
            release { callServices.freeze() }
            release { pointResumes?.clear() }
            pointResumes = null

        } finally {
            local = null
            calls = null
            formApplier = null
            publicationSink = null
            targetPublicationSink = null
            port = null
            runContext = null
            rootRouting = null
            worklist.clear()
            worklist = DeltaWorklist(flowFirst = mode.run1 && mode.markMode == MarkMode.FULL,
                batchManager = ap.takeIf { mode.run1 && mode.markMode == MarkMode.FULL })
            pending = ArrayList()
            localPublications = LinkedHashMap()
            bodyWork = null
            edgeStore = null
            initialStore = null
            temporary = RequestStorage()
            pendingTargets = ArrayList()
            resumeQueue = java.util.ArrayDeque()
            staticBatch = StaticBatch(staticSupplyProfile, ap.cancellation)
            executionReleased = true
        }
        failure?.let { throw it }
    }
}
