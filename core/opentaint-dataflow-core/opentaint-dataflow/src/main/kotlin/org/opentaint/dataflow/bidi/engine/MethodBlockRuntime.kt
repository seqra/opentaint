package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.interp.ResumeSite
import org.opentaint.dataflow.bidi.driver.ScopedTargetRows
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.*
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.ArrayDeque

/** One original method owns all block entries, local links and queued deliveries. */
internal class MethodBlockRuntime(
    private val root: RunMethodAnalyzer,
    private val port: RunnerPort<RunMethodAnalyzer>,
    private val localFactory: MethodLocalServicesFactory,
    private val callFactory: MethodCallServicesFactory,
) : MethodRootRouting {
    private val context = root.context
    private val config = port.config
    private val ap = port.shared.ap
    private val ops = port.shared.ops
    private val mode = config.mode
    private val key = root.key
    private val forward = config.direction == Direction.FORWARD
    private val graph = port.shared.contexts.graph(key, config.direction)
    val layout = port.shared.contexts.blockLayout(key)
    private val directed = layout.directed(graph.graph, backward = !forward)
    private val routesByPort = LinkedHashMap<PortId, MethodBlockRoute>().also { routes ->
        for (from in 0 until graph.graph.size) graph.graph.forEachSuccessor(from) { to ->
            directed.route(from, to).let { routes[it.port] = it }
        }
    }
    private val application = LocalRelationApplication(ops, mode)
    private val restriction = LoopOutputRestriction(ops)
    private val liveLocals = port.shared.contexts.blockLiveLocals(key)
    private val queryCounts = LoopQueryCounts()
    private val localMatchCounts = if (port.shared.n2Statistics != null) LocalSummaryMatchStatistics() else null
    private val savedSelectionCounts = if (port.shared.n2Statistics != null) SavedRecordSelectionStatistics() else null
    private var quantumQueries: LoopQueryScratch? = null
    private var localBoundaryOffers = 0L
    private var localBoundaryDrops = 0L
    private var prePublicationLocalOffers = 0L
    private var prePublicationDeadLocals = 0L
    private val observers = HashMap<Pair<BlockScope, BlockId>, LoopConsumerObservation>()
    private val entries = LinkedHashMap<BlockScope, Entry>()
    private val ready = LinkedHashSet<BlockScope>()
    private val pending = ArrayDeque<() -> Unit>()
    private val staticBoundaryRequests by lazy {
        StaticBoundaryInputRequests(ops, mode, ::forEachLocalInput, ::onRequest)
    }
    private var boundaryLimitOffers = 0L
    private var boundaryLimitCuts = 0L
    private val methodExit = if (forward) PortId.ROOT_EXIT else PortId.ROOT_ENTRY
    private val controlEntry = if (forward) PortId.ROOT_ENTRY else PortId.ROOT_EXIT
    private val exceptionExit = PortId(-4)
    private val normalEndpoints = port.shared.interpreter.exitNodes(key).filter { !it.exceptional }
        .mapTo(HashSet()) { port.shared.language.getInstIndex(it.node) }
    private val exceptionalEndpoints = port.shared.interpreter.exitNodes(key).filter { it.exceptional }
        .mapTo(HashSet()) { port.shared.language.getInstIndex(it.node) }
    private val originalEntry = port.shared.language.getInstIndex(port.shared.interpreter.entryNode(key))
    private val preparedExits = run {
        PreparedExitDirectory(layout, routesByPort, !forward, liveLocals,
            normalEndpoints + exceptionalEndpoints, originalEntry)
    }
    private var released = false

    private data class ChildPoint(val child: BlockId, val exit: PortId)
    private inner class Entry(val scope: BlockScope, val rootEntry: Boolean = false) {
        var stateOrNull: BlockRunState? = null
        val state: BlockRunState get() = checkNotNull(stateOrNull) { "A saved-only offer has no mutable block state" }
        val starts = LinkedHashSet<Int>()
        val methodStarts = LinkedHashSet<Int>()
        val requests = RequestStorage()
        val completions = LinkedHashMap<ChildPoint, ScopedEdgeStore<ChildPoint>>()
        var borrowedExceptionalNormalZero = false
        val demand: BlockBoundaryDemandView? = if (rootEntry || config.run1) null else {
            val store = checkNotNull(config.demand)
            BlockBoundaryDemandView(ap, store.scope(key, scope),
                store.scope(key, BlockScope(scope.block, controlEntry)), config.direction,
                entryRole(scope), normalOutputs(scope)) { output, original, policy ->
                store.acceptsStaticShortcutTarget(key, scope.block, output, original, policy)
            }
        }
        private val cacheValue = lazy {
            if (layout[scope.block].instructions.isEmpty()) null else
                BlockCfgDeliveryCache(layout, graph.graph, scope.block, !forward, ap.cancellation,
                    directedView = directed) { index, base ->
                    val node = graph.instructions[index]
                    context.isEnd(node) || context.isExceptionalExit(node) || context.forms.isBaseRelevant(key, node, base)
                }
        }
        val cache: BlockCfgDeliveryCache? get() = cacheValue.value
        fun existingCache(): BlockCfgDeliveryCache? = if (cacheValue.isInitialized()) cacheValue.value else null
        fun ensureState(): BlockRunState {
            stateOrNull?.let { return it }
            return BlockRunState(key, port,
                PublicationSink { _, _ -> error("An internal block cannot publish externally") },
                localFactory, callFactory,
                TargetPublicationSink { _, _ -> error("An internal block cannot publish external Targets") }, Binding(this))
                .also { stateOrNull = it }
        }
        val links = BlockSummaryLinks(ops, mode, scope, ::onData, ::onTerminal, ::onRequest, localMatchCounts)
        fun addCompletion(child: BlockId, exit: PortId, original: PremiseKey, value: Facts): List<Facts> {
            val point = ChildPoint(child, exit)
            val store = completions.getOrPut(point) {
                val directory = object : PointDirectory<ChildPoint> {
                    override val size = 1
                    override fun index(point: ChildPoint): Int {
                        check(point == childPoint) { "A child completion belongs to its exact point" }
                        return 0
                    }
                    private val childPoint = point
                }
                ScopedEdgeStore(ap, directory, config.fieldLimit,
                    flowBacked = mode.run1 && mode.markMode == MarkMode.FULL,
                    collectStatistics = port.shared.n2Statistics != null)
            }
            return store.addAll(point, original, value)
        }
    }

    init {
        check(layout.hasLoops) { "A loop-free method keeps its existing root path" }
        entries[BlockScope.ROOT] = Entry(BlockScope.ROOT, rootEntry = true).also { it.stateOrNull = root }
    }

    fun states(): List<Pair<BlockScope, BlockRunState>> = entries.mapNotNull { (scope, e) -> e.stateOrNull?.let { scope to it } }
    fun state(scope: BlockScope): BlockRunState = entries[scope]?.state ?: error("Unentered block scope $scope")
    fun scheduleRoot() { ready += BlockScope.ROOT }
    fun requireIdle() {
        check(quantumQueries == null) { "An active observer quantum cannot be sealed" }
        check(ready.isEmpty() && pending.isEmpty() && entries.values.none { it.links.hasPending || it.stateOrNull?.hasLocalWork == true }) {
            "A method has pending block work"
        }
    }

    override fun start(node: CommonInst, original: InitialAp, value: Facts) {
        check(!released)
        if (!forward && port.shared.language.getInstIndex(node) in exceptionalEndpoints) {
            // Selected HACK: the already admitted original ZERO follows the
            // real exceptional boundary and its actual discovery successors.
            root.startAt(original, node, value) { pr, result -> root.enqueueInput(node, pr, result) }
        } else routeInside(entries.getValue(BlockScope.ROOT), port.shared.language.getInstIndex(node),
            original, value, controlEntry, methodStart = true)
    }

    override fun enter(node: CommonInst, original: PremiseKey, value: Facts) = enterRoot(node, original, value)
    override fun intersectSummary(exit: PortId, original: PremiseKey, raw: Facts): List<Facts>? =
        if (quantumQueries == null) null else intersect(entries.getValue(BlockScope.ROOT), exit, original, raw)
    fun enterRoot(node: CommonInst, original: PremiseKey, value: Facts) {
        check(!released)
        if (!forward && port.shared.language.getInstIndex(node) in exceptionalEndpoints)
            root.enqueueInput(node, original, value)
        else routeInside(entries.getValue(BlockScope.ROOT), port.shared.language.getInstIndex(node), original, value, controlEntry)
    }
    override fun successors(node: CommonInst, original: PremiseKey, value: Facts) = successorsRoot(node, original, value)
    fun successorsRoot(node: CommonInst, original: PremiseKey, value: Facts) {
        val from = port.shared.language.getInstIndex(node)
        graph.forEachSuccessor(port.shared.language, node) { next ->
            val to = port.shared.language.getInstIndex(next)
            routeInside(entries.getValue(BlockScope.ROOT), to, original, value, directed.route(from, to).port)
        }
    }

    /** Call only on the method owner while its counted work reservation is held. */
    fun work(quantum: Int): Boolean {
        check(quantumQueries == null)
        quantumQueries = LoopQueryScratch(ap, queryCounts)
        return try { workQuantum(quantum) } finally {
            quantumQueries?.clear()
            quantumQueries = null
        }
    }

    private fun workQuantum(quantum: Int): Boolean {
        require(quantum > 0)
        var used = 0
        while (used < quantum) {
            ap.cancellation.checkpoint()
            if (pending.isNotEmpty()) { pending.removeFirst().invoke(); used++; continue }
            val delivery = entries.values.firstOrNull { it.links.hasPending }
            if (delivery != null) { used += delivery.links.drain(1); continue }
            val selected = ready.firstOrNull { entries.getValue(it).state.localHasZeroWork }
                ?: if (mode.run1 && mode.markMode == MarkMode.FULL)
                    ready.firstOrNull { entries.getValue(it).state.localHasFlowWork } ?: ready.firstOrNull()
                else ready.firstOrNull()
            if (selected == null) return true
            ready.remove(selected)
            val state = entries.getValue(selected).state
            if (!state.workLocal(1)) ready += selected
            used++
        }
        return ready.isEmpty() && pending.isEmpty() && entries.values.none { it.links.hasPending || it.stateOrNull?.hasLocalWork == true }
    }

    private fun entry(scope: BlockScope): Entry = entries.getOrPut(scope) { Entry(scope) }

    private fun admitTarget(e: Entry, target: Int, original: PremiseKey, value: Facts): Boolean {
        if (target in e.starts) return false
        val normal = layout.normalExit(e.scope.entry)
        if (normal != null) {
            check(if (forward) target == normal.target else normal.routes.any { directedRoute(it).to == target }) {
                "A canonical normal interface keeps its certified real targets"
            }
        } else if (e.scope.entry.ordinal >= 0)
            check(directedRoute(e.scope.entry).to == target) { "A physical entry port has one actual target" }
        if (e.starts.isNotEmpty()) {
            check(normal != null || e.scope.entry.ordinal < 0 && original.isZero && value is Reach &&
                e.stateOrNull?.initials?.all().orEmpty().all { it.isZero }) {
                "Distinct logical control targets cannot share ordinary DATA initials"
            }
        }
        e.starts += target
        return true
    }

    private fun queue(action: () -> Unit) {
        pending += action
        port.enqueue(root)
    }

    private inner class Binding(private val e: Entry) : BlockRuntimeBinding {
        override val scope get() = e.scope
        override val context get() = this@MethodBlockRuntime.context
        override val points = object : PointDirectory<CommonInst> {
            override val size get() = layout[e.scope.block].instructions.size
            override fun index(point: CommonInst): Int {
                val index = port.shared.language.getInstIndex(point)
                check(layout.ownerOf(index) == e.scope.block)
                return layout.localIndex(index)
            }
        }
        override val bodyWork get() = root.sharedBodyWork
        override val sourceHits get() = root.sourceHits
        override val sinkSeeds get() = root.sinkSeeds
        override val demand get() = e.demand
        override fun intersectSummary(exit: PortId, original: PremiseKey, raw: Facts): List<Facts>? =
            if (quantumQueries == null) null else intersect(e, exit, original, raw)
        override fun keepLocalConclusion(exit: PortId, value: Facts): Boolean =
            this@MethodBlockRuntime.keepLocalConclusion(e.scope.block, exit, value)
        override fun prepareExit(exit: PortId, base: org.opentaint.dataflow.ap.ifds.AccessPathBase): PreparedExit {
            val prepared = preparedExits.getOrPrepare(e.scope, exit, base)
            if (base is org.opentaint.dataflow.ap.ifds.AccessPathBase.LocalVar) {
                prePublicationLocalOffers++
                if (prepared === PreparedExit.DeadData) prePublicationDeadLocals++
            }
            return prepared
        }
        override fun schedule() { ready += scope; port.enqueue(root) }
        override fun start(state: BlockRunState, original: InitialAp, value: Facts) {
            check(original.isZero || e.starts.size <= 1 || layout.normalExit(scope.entry) != null) { "A DATA initial has one exact entry target" }
            if (isEmptyBlock(scope.block)) {
                val start = e.starts.singleOrNull()
                if (start != null && start in e.methodStarts)
                    state.startAt(original, graph.instructions[start], value)
                else state.retainBlockSummary(scope.entry, original, value)
                return
            }
            for (target in e.starts.toList()) queue { startEntryTarget(e, state, target, original, value) }
        }
        override fun startResult(state: BlockRunState, node: CommonInst, original: PremiseKey, value: Facts) {
            if (isEmptyBlock(scope.block)) state.retainBlockSummary(scope.entry, original, value)
            else routeInside(e, port.shared.language.getInstIndex(node), original, value, scope.entry)
        }
        override fun successors(state: BlockRunState, node: CommonInst, original: PremiseKey, value: Facts) {
            val from = port.shared.language.getInstIndex(node)
            for (next in checkNotNull(e.cache).after(from, value.base)) dispatch(e, next, original, value)
        }
        override fun publish(state: BlockRunState, exit: PortId, publications: List<Publication>) {
            e.links.publish(exit, publications)
            port.enqueue(root)
        }
        override fun publishTargets(state: BlockRunState, targets: TargetBatch) {
            e.links.publishTargets(targets)
            port.enqueue(root)
        }
        override fun borrowRequests(input: Facts) = e.requests.borrowMatchingRows(input, ap.cancellation::checkpoint)
        override fun borrowRequest(slot: Run1Slot) = e.requests.borrow(slot)
        override fun commitRequests(state: BlockRunState, temporary: RequestStorage) {
            val fresh = LinkedHashMap<Run1Slot, RequestMarkSet>()
            for ((slot, marks) in temporary.pendingRows()) {
                val delta = e.requests.addAll(slot, marks, ap.cancellation::checkpoint)
                if (!delta.isEmpty) fresh[slot] = delta
            }
            if (fresh.isEmpty()) return
            e.links.forEachInput { link, value -> applyRequests(e, link, value, fresh) }
        }
        override fun staticMarkRequest(initial: InitialAp, mark: TaintMark) {
            if (config.run1 && forward && scope.entry == PortId.ROOT_EXIT)
                staticBoundaryRequests.request(scope, initial, mark)
        }
        override fun staticTicket(): Long = root.allocateStaticTicket(scope)
        override fun routeStaticToExit(state: BlockRunState, node: CommonInst, original: PremiseKey, value: Facts) {
            state.retainBlockSummary(PortId.STATIC_SHORTCUT, original, value)
        }
        override fun methodBoundary(state: BlockRunState, node: CommonInst, original: PremiseKey, value: Facts, summary: Boolean) {
            state.endAt(original, node, value, summary)
        }
        override fun deliveryStatistics(): BlockDeliveryStatistics? = e.existingCache()?.let {
            BlockDeliveryStatistics(it.hits, it.searches, it.visitedNodes, it.destinations, it.maxWidth)
        }
    }

    private fun startEntryTarget(e: Entry, state: BlockRunState, target: Int, original: PremiseKey, value: Facts) {
        if (isEmptyBlock(e.scope.block)) {
            // A shared normal interface can discover another real reverse
            // predecessor after this identity region already admitted its
            // initial. Replay the same logical identity as Binding.start;
            // the physical predecessor belongs to the adjacent region.
            if (target in e.methodStarts) state.startAt(original, graph.instructions[target], value)
            else state.retainBlockSummary(e.scope.entry, original, value)
        } else if (target in e.methodStarts && layout[e.scope.block].isLeaf)
            state.startAt(original, graph.instructions[target], value)
        else routeInside(e, target, original, value, e.scope.entry, methodStart = target in e.methodStarts)
    }

    private fun routeInside(parent: Entry, target: Int, original: PremiseKey, value: Facts,
                            arrival: PortId, passedEmpty: Boolean = false, methodStart: Boolean = false) {
        ap.cancellation.checkpoint()
        val block = layout[parent.scope.block]
        if (block.isLeaf) {
            check(layout.ownerOf(target) == block.id)
            for (next in checkNotNull(parent.cache).targets(target, value.base)) dispatch(parent, next, original, value)
            return
        }
        val next = block.children.single { layout.contains(it, target) }
        val emptyPrefix = if (forward) block.before else block.after
        val arrivalRoute = routesByPort[arrival]
        if (!passedEmpty && next == block.loop && emptyPrefix != null &&
            isEmptyBlock(emptyPrefix) && arrivalRoute?.feedbackLoop != next && arrivalRoute?.discovery != true) {
            offerChild(parent, emptyPrefix, target, original, value, arrival, methodStart)
        } else offerChild(parent, next, target, original, value, arrival, methodStart)
    }

    private fun dispatch(e: Entry, target: BlockDeliveryTarget, original: PremiseKey, value: Facts) {
        when (target) {
            is BlockDeliveryTarget.Statement -> e.state.enqueueInput(graph.instructions[target.index], original, value)
            is BlockDeliveryTarget.Boundary -> e.state.retainBlockSummary(outputPort(target.route.port, e.scope.block), original, value)
        }
    }

    private fun offerChild(parent: Entry, child: BlockId, target: Int, original: PremiseKey, value: Facts, arrival: PortId,
                           methodStart: Boolean = false) {
        // DATA/native rows keep the actual ingress, including ZERO identity
        // relations. A typed terminal endpoint is not a replacement for it.
        val logical = inputPort(arrival, parent.scope.block, child)
        val scope = BlockScope(child, logical)
        val childEntry = entry(scope)
        if (methodStart) childEntry.methodStarts += target
        val link = LocalLink(parent.scope, logical, original, value.layer, scope)
        if (LoopPipelineTrace.enabled(config.index, key)) LoopPipelineTrace.record(config.index, key, "local-offer") {
            catalog(ap); text("parent", parent.scope.toString()); text("child", scope.toString())
            number("point", logical.ordinal); number("target", target)
            premise("P", original); facts("offered", value)
        }
        replaySaved(childEntry, link, value)
        val admission = if (config.run1) null else childEntry.demand!!.admission(value, config.admissionPolicy)
        val initials = admission?.initials
        if (initials != null && initials.isEmpty()) return
        if (admission?.borrowedExceptionalNormalZero == true) childEntry.borrowedExceptionalNormalZero = true
        val state = childEntry.ensureState()
        val admittedTarget = admitTarget(childEntry, target, original, value)
        if (admittedTarget && layout.normalExit(scope.entry) != null) {
            // All these targets are true reverse predecessors of the SAME
            // original normal join. A previously admitted fact reaches each.
            for (initial in state.initials.admissions()) {
                val intrinsic = ops.startFact(initial.initial, mode)
                val start = state.forceRun1Layer(initial.initial,
                    intrinsic.withLayer(intrinsic.layer or (initial.layer == Layer.DEMAND)))
                queue { startEntryTarget(childEntry, state, target, initial.initial, start) }
            }
        } else if (admittedTarget && state.initials.all().any { it.isZero } && original.isZero && value is Reach)
            queue { startEntryTarget(childEntry, state, target, ap.zero, state.forceRun1Layer(ap.zero, ops.startFact(ap.zero, mode))) }
        childEntry.links.offer(link, value)
        if (childEntry.links.hasPending) port.enqueue(root)
        if (config.run1) {
            checkNotNull(state.abstraction).emit(original, value)
            if (value is FlowTree) applyRequests(childEntry, link, value, childEntry.requests.pendingRows())
        } else for (initial in checkNotNull(initials)) state.addInitial(initial)
    }

    fun offerStaticAnswer(link: LocalLink, original: InitialAp, value: Facts) {
        val child = entries.getValue(link.child)
        val selected = link.copy(original = original, layer = value.layer)
        replaySaved(child, selected, value)
        child.links.offer(selected, value)
        // This callback can run in a StaticOwner event while the method is
        // idle. A fresh link can queue current-summary deliveries even when
        // abstraction.emit finds only initials which already exist. Keep a
        // counted method Work reservation for those deliveries independently
        // of initial admission.
        if (child.links.hasPending) port.enqueue(root)
        if (forward && child.scope.entry == PortId.ROOT_EXIT && value.base == STATIC) {
            // The selected outer link retains CF/T -> CG/T. The local span's
            // own initial is CG/T; propagate this real supplied operation input
            // through the same identity continuations used by the raw write.
            for (scalar in annotatedLoopScalars(ops, value)) {
                val initial = concreteStaticResumeInitial(ap, ops.leaves(scalar).single())
                routeStaticBoundaryInput(child, initial, scalar)
            }
        } else checkNotNull(child.state.abstraction).emit(original, value)
    }

    private fun applyRequests(child: Entry, link: LocalLink, actual: Facts, rows: RequestRows) {
        if (actual is TaintTree) {
            checkNotNull(child.state.abstraction).emit(link.original, actual)
            return
        }
        if (actual !is FlowTree || !link.original.isFlow) return
        for ((slot, marks) in rows) {
            if (!slotMatches(slot, actual)) continue
            val cursor = marks.cursor()
            while (!cursor.isComplete) cursor.step(256) { mark -> onRequest(link, actual, mark) }
        }
    }

    private fun onRequest(link: LocalLink, actual: Facts, mark: TaintMark) {
        if (!config.run1 || actual !is FlowTree) return
        val original = link.original as? InitialAp ?: return
        if (original.mark !is MarkSlot.Star) return
        if (original.base == STATIC) root.requestLocalStaticInput(link, actual, mark)
        else entries.getValue(link.parent).state.addMarkRequest(original, mark)
    }

    private fun savedRows(scope: BlockScope, actual: Facts): Sequence<SavedRecordSelection> =
        selectSavedRecords(config.records, key, scope, actual, ops, config.direction, savedSelectionCounts).asSequence()

    private fun replaySaved(child: Entry, link: LocalLink, actual: Facts) {
        for (selected in savedRows(child.scope, actual)) {
            val record = selected.record
            val exit = checkNotNull(record.exitIn(config.direction))
            if (record.direction == config.direction) {
                preparedExits.getOrPrepare(child.scope, if (isEmptyBlock(child.scope.block)) child.scope.entry else exit,
                    record.conclusion.base)
                savedSelectionCounts?.let { it.replayDirectMatches++ }
                val lanes = application.matchRecord(actual, link.original, record) ?: continue
                for (scalar in annotatedLoopScalars(ops, record.conclusion)) {
                    val row = Record(key, record.direction, record.premise, scalar)
                    applySaved(child, link, actual, exit, record.premise, ops.leaves(scalar).single()) {
                        out -> application.applyMatchedRecord(lanes, link.original, row, out)
                    }
                }
            } else {
                selected.forEachReversedAt(actual, ops) { view, protected ->
                    applySavedView(child, link, actual, exit, view, protected)
                }
            }
        }
        for ((row, member) in config.normalTargets.candidates(key, child.scope, link.original, actual, mode))
            child.links.replaySavedTarget(link, actual, row, member)
        if (child.links.hasPending) port.enqueue(root)
    }

    private fun applySaved(child: Entry, link: LocalLink, actual: Facts, exit: PortId,
                           row: PremiseKey, geometry: Pattern, apply: (LocalRelationOut) -> Unit) {
        apply(object : LocalRelationOut {
            override fun data(original: PremiseKey, value: Facts) = onData(link, exit, row, geometry, original, value)
            override fun target(original: PremiseKey, target: Target) = onTerminal(link, original, target)
            override fun markRequest(mark: TaintMark) = onRequest(link, actual, mark)
        })
    }

    private fun applySavedView(child: Entry, link: LocalLink, actual: Facts, exit: PortId,
                               view: RecordLeafView, protected: Boolean) {
        preparedExits.getOrPrepare(child.scope, if (isEmptyBlock(child.scope.block)) child.scope.entry else exit, view.result.fact.base)
        if (LoopPipelineTrace.enabled(config.index, key)) LoopPipelineTrace.record(config.index, key, "local-reversed-record") {
            catalog(ap); text("parent", link.parent.toString()); text("child", link.child.toString())
            number("exit", exit.ordinal); number("point", link.point.ordinal)
            premise("P", link.original); facts("offered", actual)
            pattern("I", view.premise); pattern("O", Pattern(view.result.fact, view.result.exclusion))
            flag("resultDemand", view.result.demand); flag("protected", protected)
        }
        val needsGate = view.premise.fact.base != org.opentaint.dataflow.ap.ifds.AccessPathBase.Zero &&
            loopFieldLength(Pattern(view.result.fact, view.result.exclusion)) > loopFieldLength(view.premise)
        application.applyRecordView(actual, link.original, view, protected, object : LocalRelationOut {
            override fun data(original: PremiseKey, value: Facts) = onApplied(link, exit, needsGate, original, value)
            override fun target(original: PremiseKey, target: Target) = onTerminal(link, original, target)
            override fun markRequest(mark: TaintMark) = onRequest(link, actual, mark)
        })
    }

    private fun onData(link: LocalLink, exit: PortId, row: PremiseKey, geometry: Pattern,
                       original: PremiseKey, value: Facts) {
        if (LoopPipelineTrace.enabled(config.index, key)) LoopPipelineTrace.record(config.index, key, "local-relation") {
            catalog(ap); text("parent", link.parent.toString()); text("child", link.child.toString())
            number("exit", exit.ordinal); number("point", link.point.ordinal)
            premise("I", row); pattern("O", geometry); premise("P", original); facts("applied", value)
        }
        onApplied(link, exit, !row.isZero && loopSummaryGrows(row, geometry), original, value)
    }

    private fun onApplied(link: LocalLink, exit: PortId, needsGate: Boolean, original: PremiseKey, value: Facts) {
        val parent = entries.getValue(link.parent)
        val child = layout[link.child.block]
        val completionExit = if (isEmptyBlock(child.id)) link.point else exit
        val routes = preparedExits.getOrPrepare(link.child, completionExit, value.base)
        if (LoopPipelineTrace.enabled(config.index, key)) LoopPipelineTrace.record(config.index, key, "local-applied") {
            catalog(ap); text("parent", link.parent.toString()); text("child", link.child.toString())
            number("exit", exit.ordinal); number("point", completionExit.ordinal)
            premise("P", original); facts("value", value); flag("needsGate", needsGate)
            text("prepared", routes.javaClass.simpleName)
        }
        if (routes === PreparedExit.DeadData) return
        // Reuse the ordinary global AP bound before a local result is stored
        // or offered onward. A saved relation can add its own prefix to the
        // caller suffix, just as a real call summary does. This is not a new
        // loop cut and does not invoke a physical instruction/rule cut hook.
        boundaryLimitOffers++
        val depth = when (value) {
            is Reach -> 0
            is FlowTree -> value.root.boundedDepth
            is TaintTree -> value.root.boundedDepth
        }
        if (depth > config.fieldLimit) boundaryLimitCuts++
        ops.limit(value, config.fieldLimit, object : ApOut {
            override fun result(bounded: Facts) {
                val values = if (!child.isLoop || exit.ordinal < 0) listOf(bounded) else
                    restriction.restrict(config.run1, needsGate, bounded, LoopRestrictionSession(ops, config.admissionPolicy,
                        { candidate -> observe(parent, child, link, exit, original, candidate) },
                        { actual -> observers[parent.scope to child.id]?.precisionCursors(actual) }))
                for (kept in values) {
                    if (LoopPipelineTrace.enabled(config.index, key)) LoopPipelineTrace.record(config.index, key, "local-kept") {
                        catalog(ap); text("parent", link.parent.toString()); text("child", link.child.toString())
                        number("exit", exit.ordinal); number("point", completionExit.ordinal)
                        premise("P", original); facts("kept", kept)
                    }
                    val fresh = parent.addCompletion(child.id, completionExit, original, kept)
                    if (LoopPipelineTrace.enabled(config.index, key)) LoopPipelineTrace.record(config.index, key, "local-completion") {
                        catalog(ap); text("parent", link.parent.toString()); text("child", link.child.toString())
                        number("exit", exit.ordinal); number("point", completionExit.ordinal)
                        premise("P", original); facts("offered", kept); flag("fresh", fresh.isNotEmpty())
                        fresh.forEachIndexed { index, delta -> facts("delta$index", delta) }
                    }
                    for (delta in fresh) queue { routeCompleted(parent, child, link, exit, original, delta, routes) }
                }
            }
            override fun markRequest(mark: TaintMark) = error("A global local-boundary field limit cannot request a mark")
        })
    }

    private fun onTerminal(link: LocalLink, original: PremiseKey, target: Target) {
        queue { entries.getValue(link.parent).state.emitTarget(original, target) }
    }

    private fun routeCompleted(parent: Entry, child: MethodBlock, link: LocalLink, exit: PortId,
                               original: PremiseKey, value: Facts, prepared: PreparedExit) {
        if (isEmptyBlock(child.id)) {
            if (link.point.ordinal >= 0) for (route in preparedRoutes(prepared, link.point)) {
                if (route.feedbackLoop == parent.scope.block)
                    parent.state.retainBlockSummary(route.port, original, value)
                else if (layout.contains(parent.scope.block, route.to))
                    routeInside(parent, route.to, original, value, link.point, passedEmpty = true)
                else parent.state.retainBlockSummary(outputPort(route.port, parent.scope.block), original, value)
            } else for (target in entries.getValue(link.child).starts.toList()) {
                if (prepared is PreparedExit.ActualStarts && !prepared.allows(target)) continue
                if (layout.contains(parent.scope.block, target))
                    routeInside(parent, target, original, value, link.point, passedEmpty = true)
                else parent.state.retainBlockSummary(link.point, original, value)
            }
            return
        }
        if (exit == PortId.STATIC_SHORTCUT) {
            check(config.run1 && forward && value.base == STATIC) {
                "Only an unprocessed run-1 static output uses the shortcut channel"
            }
            if (parent.scope == BlockScope.ROOT) routeStaticBoundaryInput(parent, original, value)
            else parent.state.retainBlockSummary(PortId.STATIC_SHORTCUT, original, value)
            return
        }
        if (exit.ordinal < 0) {
            if (parent.scope == BlockScope.ROOT) {
                val node = if (exit == exceptionExit) port.shared.interpreter.exitNodes(key).single { it.exceptional }.node
                    else if (forward) context.normalExit else port.shared.interpreter.entryNode(key)
                // ROOT_EXIT comes from an actual completed handler, whether
                // its input used normal J or the private operation continuation.
                root.finishBoundMethodBoundary(original, node, value, summary = exit != exceptionExit)
            } else parent.state.retainBlockSummary(exit, original, value)
            return
        }
        for (route in preparedRoutes(prepared, exit)) {
            if (layout.contains(parent.scope.block, route.to) && route.feedbackLoop != parent.scope.block)
                routeInside(parent, route.to, original, value, exit)
            else if (parent.scope == BlockScope.ROOT) error("An original CFG edge cannot leave its method layout")
            else {
                val suffixId = if (forward) layout[parent.scope.block].after else layout[parent.scope.block].before
                val suffix = suffixId?.let { layout[it] }
                if (suffix != null && isEmptyBlock(suffix.id) && child.id != suffix.id)
                    offerChild(parent, suffix.id, route.to, original, value, exit)
                else parent.state.retainBlockSummary(outputPort(route.port, parent.scope.block), original, value)
            }
        }
    }

    private fun preparedRoutes(prepared: PreparedExit, exit: PortId): List<MethodBlockRoute> = when (prepared) {
        is PreparedExit.Routes -> prepared.routes
        PreparedExit.DeadData -> emptyList()
        else -> deliveryRoutes(exit) // Unknown interfaces keep their established native dispatch.
    }

    private fun entryRole(scope: BlockScope): BlockEntryRole {
        if (layout.normalExit(scope.entry) != null) return BlockEntryRole.NORMAL_INTERFACE
        val route = routesByPort[scope.entry] ?: return BlockEntryRole.MID_BLOCK
        if (route.discovery || !forward && route.from in exceptionalEndpoints || forward && route.to in exceptionalEndpoints)
            return BlockEntryRole.EXCEPTIONAL_INTERFACE
        val crossesNormalInterface = !layout.contains(scope.block, route.from) && layout.contains(scope.block, route.to) ||
            route.feedbackLoop == scope.block || isEmptyBlock(scope.block)
        val actualRootNormal = if (forward) route.from == originalEntry else route.from in normalEndpoints
        return if (crossesNormalInterface || actualRootNormal) BlockEntryRole.NORMAL_INTERFACE else BlockEntryRole.MID_BLOCK
    }

    private fun normalOutputs(scope: BlockScope): Set<PortId> = buildSet {
        if (isEmptyBlock(scope.block)) {
            if (scope.entry in routesByPort || layout.normalExit(scope.entry) != null) add(scope.entry)
            return@buildSet
        }
        for (route in routesByPort.values) {
            if (route.discovery || forward && route.to in exceptionalEndpoints) continue
            if (layout.contains(scope.block, route.from) &&
                (!layout.contains(scope.block, route.to) || route.feedbackLoop == scope.block || isRootEnd(route.to)))
                add(outputPort(route.port, scope.block))
        }
    }

    private fun isRootEnd(index: Int): Boolean = graph.instructions[index].let {
        context.isEnd(it) || context.isExceptionalExit(it)
    }

    /** An empty prefix still has a genuine identity/rule interface. Physical endpoints own transfers. */
    private fun isEmptyBlock(block: BlockId): Boolean = layout[block].let {
        it.isLeaf && !it.isLoop && it.instructions.isEmpty()
    }

    /** Continue a real run-1 write shortcut at its original normal-exit operation.
     * ROOT_EXIT is the selected operation-local static continuation address, not
     * a method-entry seed. Its local rows therefore include the real exit rules.
     */
    private fun routeStaticBoundaryInput(parent: Entry, original: PremiseKey, value: Facts) {
        check(config.run1 && forward && value.base == STATIC)
        val target = port.shared.language.getInstIndex(context.normalExit)
        val block = layout[parent.scope.block]
        if (block.isLeaf) {
            for (scalar in annotatedLoopScalars(ops, value)) {
                val leaf = ops.leaves(scalar).single()
                val initial = if (value is TaintTree) concreteStaticResumeInitial(ap, leaf) else {
                    check(leaf.fact.path.size >= 2) { "A static FLOW continuation names a field" }
                    ap.initial(Pattern(leaf.fact.copy(path = leaf.fact.path.take(2),
                        tail = Tail.STAR, mark = MarkSlot.STAR), ExclusionSet.Empty))
                }
                parent.state.installPoint(initial, scalar,
                    ResumeSite.BoundaryInput(parent.state.operation(context.normalExit), atStart = false), null)
            }
            return
        }
        val childId = block.children.single { layout.contains(it, target) }
        val child = entry(BlockScope(childId, PortId.ROOT_EXIT))
        val link = LocalLink(parent.scope, PortId.ROOT_EXIT, original, value.layer, child.scope)
        replaySaved(child, link, value)
        child.ensureState()
        admitTarget(child, target, original, value)
        child.links.offer(link, value)
        if (child.links.hasPending) port.enqueue(root)
        // A local operation input keeps its own initial, exactly as an existing
        // physical static-read reply. It does not enter Run1Abstraction.
        for (scalar in annotatedLoopScalars(ops, value)) {
            val leaf = ops.leaves(scalar).single()
            val initial = if (value is TaintTree) concreteStaticResumeInitial(ap, leaf) else
                ap.initial(Pattern(leaf.fact.copy(path = leaf.fact.path.take(2),
                    tail = Tail.STAR, mark = MarkSlot.STAR), ExclusionSet.Empty))
            routeStaticBoundaryInput(child, initial, scalar)
        }
    }

    /** Only the interface currently being crossed changes the port view.
     * An inner normal completion can retain an enclosing loop's repeat role.
     */
    private fun outputPort(actual: PortId, block: BlockId): PortId =
        layout.normalExitsForRoute(actual).filter { normal ->
            val adjacent = layout[normal.loop].parent?.let { layout[it].after }
            layout.isAncestor(normal.loop, block) || adjacent?.let { layout.isAncestor(it, block) } == true
        }.maxByOrNull { layout[it.loop].depth }?.id ?: actual

    private fun inputPort(actual: PortId, parent: BlockId, child: BlockId): PortId {
        if (layout.normalExit(actual) != null) return actual
        return layout.normalExitsForRoute(actual).filter { normal ->
            layout.isAncestor(normal.loop, child) ||
                layout[normal.loop].parent == parent && layout[parent].after == child
        }.maxByOrNull { layout[it.loop].depth }?.id ?: actual
    }

    /** Same actual output adapter for live delivery and the pure paired observer. */
    private fun enclosingPorts(exit: PortId, parent: BlockId): List<PortId> =
        if (exit.ordinal < 0) listOf(exit) else deliveryRoutes(exit)
            .map { outputPort(it.port, parent) }.distinct()

    /** Forward has one certified target; reverse restores EVERY real predecessor. */
    private fun deliveryRoutes(portId: PortId): List<MethodBlockRoute> =
        layout.normalExit(portId)?.routes?.map(::directedRoute) ?: listOf(directedRoute(portId))

    private fun directedRoute(portId: PortId): MethodBlockRoute =
        routesByPort[portId] ?: error("Unknown directed block port $portId")

    private fun keepAlongRoute(route: MethodBlockRoute, value: Facts, count: Boolean = true): Boolean {
        val local = value.base as? org.opentaint.dataflow.ap.ifds.AccessPathBase.LocalVar ?: return true
        if (count) localBoundaryOffers++
        // The actual endpoint handler must run before filtering its completed DATA.
        val keep = isRootEnd(route.to) || route.to == originalEntry ||
            liveLocals?.mayFollow(!forward, route, local.idx) != false
        if (!keep && count) localBoundaryDrops++
        return keep
    }

    private fun keepLocalConclusion(block: BlockId, exit: PortId, value: Facts, count: Boolean = true): Boolean {
        if (value.base !is org.opentaint.dataflow.ap.ifds.AccessPathBase.LocalVar) return true
        if (count) localBoundaryOffers++
        // Synthetic/unknown interfaces retain the native path until a real
        // continuation is available. A missing mask is not an empty mask.
        if (exit.ordinal < 0 || liveLocals == null) return true
        val normal = layout.normalExit(exit)
        if (normal == null && exit !in routesByPort) return true
        val keep = deliveryRoutes(exit).any { keepAlongRoute(it, value, count = false) }
        if (!keep && count) localBoundaryDrops++
        return keep
    }

    private fun plan(parent: Entry, exit: PortId, original: PremiseKey, templates: List<Pattern>): PreparedLocalDataPlan? {
        val scratch = quantumQueries ?: return null
        val view: Any = if (parent.rootEntry) checkNotNull(config.demand) else checkNotNull(parent.demand)
        return scratch.plan(view, exit, original, templates, config.admissionPolicy) {
            if (parent.rootEntry) checkNotNull(config.demand).prepareDataPlan(key, templates, config.admissionPolicy) { queryCounts.planChecks++ }
            else (parent.demand as? PreparedScopeDemandView)?.prepareDataPlan(exit, templates, config.admissionPolicy) { queryCounts.planChecks++ }
        }
    }

    private fun intersect(parent: Entry, exit: PortId, original: PremiseKey, value: Facts): List<Facts> {
        if (value !is Reach && !original.isZero && original.size <= 2048) {
            val prepared = plan(parent, exit, original, original.members.map { it.toPattern() })
            if (prepared != null) {
                prepared.intersect(original, value)?.let { queryCounts.c5PreparedQueries++; return it }
                queryCounts.c5ReferenceFallbacks++
            }
        }
        queryCounts.c5NativeQueries++
        return if (parent.rootEntry) checkNotNull(config.demand).intersect(key, original, value, config.admissionPolicy)
            else checkNotNull(parent.demand).intersect(exit, original, value, config.admissionPolicy)
    }

    private fun skipEmptyDataReplay(parent: Entry, original: PremiseKey, actual: Facts,
                                    saved: LoopObservedRecord): Boolean {
        val record = saved.record
        if (parent.rootEntry || mode.run1 || original.isZero || original.size > 2048 || actual is Reach ||
            original.isFlow != (actual is FlowTree) || record.direction != config.direction ||
            record.premise.isZero || record.premise.tail == Tail.ANY_TAINT || record.conclusion is Reach ||
            record.conclusion.base == org.opentaint.dataflow.ap.ifds.AccessPathBase.Zero ||
            record.premise.isFlow != (record.conclusion is FlowTree) ||
            original.isFlow && record.conclusion !is FlowTree) return false
        val templates = normalizedOriginalTemplates(original, flow = original.isFlow)
        val prepared = plan(parent, saved.enclosingExit, original, templates) ?: return false
        if (!prepared.emptyForBase(record.conclusion.base)) return false
        queryCounts.emptyReplays++
        return true
    }

    private fun observe(parent: Entry, loop: MethodBlock, link: LocalLink, exit: PortId,
                        original: PremiseKey, value: Facts): LoopObservation<LoopEnclosingResult> {
        val observer = observers.getOrPut(parent.scope to loop.id) {
        val adjacentId = checkNotNull(if (forward) layout[parent.scope.block].after else layout[parent.scope.block].before)
        val adjacent = layout[adjacentId]
        val adjacentScopes = routesByPort.values.asSequence().filter { route ->
            layout.contains(loop.id, route.from) &&
                (layout.contains(adjacentId, route.to) || isEmptyBlock(adjacent.id) &&
                    (!layout.contains(parent.scope.block, route.to) || route.feedbackLoop == parent.scope.block))
        }.map { BlockScope(adjacentId, inputPort(it.port, parent.scope.block, adjacentId)) }.toSet()
        val repeatScopes = loop.repeatPorts.map { BlockScope(loop.id, it) }.toSet()
        val adjacentDemands = adjacentScopes.associateWith { checkNotNull(config.demand).scope(key, it) }
        val repeatDemands = repeatScopes.associateWith { checkNotNull(config.demand).scope(key, it) }
        fun initials(scope: BlockScope, demand: ScopeDemandView, actual: Facts): Set<AdmittedInitial> {
            if (!keepLocalConclusion(scope.block, scope.entry, actual, count = false)) return emptySet()
            quantumQueries?.let { return it.initials(demand, actual, config.admissionPolicy) }
            ap.cancellation.checkpoint(); queryCounts.c2Queries++; queryCounts.c2Native++
            return demand.initials(actual, config.admissionPolicy).also { queryCounts.c2Rows += it.size }
        }
        fun labelled(actual: Facts): Set<LoopLabelledAdmission> = buildSet {
            for ((scope, demand) in adjacentDemands) for (initial in initials(scope, demand, actual))
                add(LoopLabelledAdmission(scope, LoopAdmissionFamily.ADJACENT, initial))
            for ((scope, demand) in repeatDemands) for (initial in initials(scope, demand, actual))
                add(LoopLabelledAdmission(scope, LoopAdmissionFamily.REPEAT, initial))
        }
        val enclosingDemand = parent.demand
        val views = LoopConsumerViews(parent.scope, parent.rootEntry,
            { actual -> adjacentDemands.flatMap { (scope, demand) -> initials(scope, demand, actual) }.toSet() },
            { actual -> repeatDemands.flatMap { (scope, demand) -> initials(scope, demand, actual) }.toSet() },
            { actual -> adjacentScopes.asSequence().flatMap { scope -> savedRows(scope, actual) }
                .flatMap { selected -> enclosingPorts(checkNotNull(selected.record.exitIn(config.direction)), parent.scope.block)
                    .asSequence().map { LoopObservedRecord(selected.record, it, selected) } } },
            { pr, actual -> adjacentScopes.asSequence().flatMap { scope ->
                config.normalTargets.candidates(key, scope, pr, actual, mode).asSequence()
            }.map { (row, member) -> LoopObservedTarget(row, member, methodExit) } },
            { portId, pr, actual -> intersect(parent, portId, pr, actual) },
            { portId, pr -> if (parent.rootEntry) checkNotNull(config.demand).acceptsTarget(key, pr, config.admissionPolicy)
                else checkNotNull(enclosingDemand).acceptsTarget(portId, pr, config.admissionPolicy) },
            { pr, id -> config.normalTargets.contains(key, if (parent.rootEntry) null else parent.scope, pr, id) },
            port.shared.interpreter::isSummaryBase, ::labelled,
            { pr, actual -> if (parent.rootEntry) root.adjustObservedMethodExit(pr, actual) else actual },
            admissionBundle = { actual -> LoopAdmissionBundle(
                { adjacentDemands.flatMap { (scope, demand) -> initials(scope, demand, actual).map {
                    LoopLabelledAdmission(scope, LoopAdmissionFamily.ADJACENT, it) } } },
                { repeatDemands.flatMap { (scope, demand) -> initials(scope, demand, actual).map {
                    LoopLabelledAdmission(scope, LoopAdmissionFamily.REPEAT, it) } } }) },
            keepEnclosingData = { output, actual -> keepLocalConclusion(parent.scope.block, output, actual, count = false) },
            skipEmptyDataReplay = { pr, actual, saved -> skipEmptyDataReplay(parent, pr, actual, saved) },
            precisionCursors = { actual ->
                val packet = ap.factsOf(actual.fact, actual.exclusion, Layer.DEMAND)
                buildList {
                    for ((family, demands) in listOf(LoopAdmissionFamily.ADJACENT to adjacentDemands,
                                                     LoopAdmissionFamily.REPEAT to repeatDemands))
                        for ((scope, demand) in demands) {
                            if (!keepLocalConclusion(scope.block, scope.entry, packet, count = false)) continue
                            val cursors = (demand as? EntryPrecisionView)?.precisionCursors(actual, config.admissionPolicy)
                                ?: continue
                            for (cursor in cursors) add(LoopPrecisionCursor(scope, family, cursor))
                        }
                }
            })
        LoopConsumerObservation(ops, mode, views)
        }
        val observation = observer.observe(original, value)
        if (LoopPipelineTrace.enabled(config.index, key)) LoopPipelineTrace.record(config.index, key, "loop-observation") {
            catalog(ap); text("parent", parent.scope.toString()); number("loop", loop.id.ordinal)
            number("exit", exit.ordinal); premise("P", original); facts("F", value)
            number("adjacentCount", observation.adjacentInitials.size)
            number("repeatCount", observation.repeatInitials.size)
            number("labelCount", observation.labelledAdmissions.size)
            number("enclosingCount", observation.enclosingResults.size)
            for ((index, admitted) in observation.adjacentInitials.withIndex()) {
                premise("adjacent${index}Initial", admitted.initial); text("adjacent${index}Layer", admitted.layer.name)
            }
            for ((index, admitted) in observation.repeatInitials.withIndex()) {
                premise("repeat${index}Initial", admitted.initial); text("repeat${index}Layer", admitted.layer.name)
            }
            for ((index, labelled) in observation.labelledAdmissions.withIndex()) {
                text("label${index}Scope", labelled.scope.toString()); text("label${index}Family", labelled.family.name)
                premise("label${index}Initial", labelled.admitted.initial); text("label${index}Layer", labelled.admitted.layer.name)
            }
            for ((index, result) in observation.enclosingResults.withIndex()) when (result) {
                is LoopEnclosingResult.Data -> {
                    text("result${index}Scope", result.scope.toString()); number("result${index}Exit", result.exit.ordinal)
                    premise("result${index}P", result.original); pattern("result${index}F", result.member.pattern)
                    text("result${index}Layer", result.member.layer.name); flag("result${index}Protected", result.member.nonSubsumable)
                }
                is LoopEnclosingResult.Terminal -> {
                    text("result${index}Scope", result.scope.toString()); number("result${index}Exit", result.exit.ordinal)
                    premise("result${index}P", result.original); text("result${index}Target", result.target.toString())
                }
            }
        }
        return observation
    }

    /** Barrier-only scalar census. It retains no edge, premise or form snapshot. */
    fun diagnosticStatistics(): String {
        val counts = restriction.statistics
        val gapDetails = if (layout.normalExitGaps.isEmpty()) "" else " normalGapDetails=" +
            layout.normalExitGaps.joinToString("|") {
                "${it.loop.ordinal}:headers[${it.headers.joinToString(",")}]:continuations[${it.continuations.joinToString(",")}]"
            }
        return "layoutBlocks=${layout.blocks.size} loops=${layout.blocks.count { it.isLoop }} " +
            "normalExitGaps=${layout.normalExitGaps.size} " +
            "maxDepth=${layout.blocks.maxOfOrNull { it.depth } ?: 0} entryScopes=${entries.size} " +
            "instantiatedStates=${entries.values.count { it.stateOrNull != null }} " +
            "liveInputGroups=${entries.values.sumOf { it.links.inputGroups.toLong() }} " +
            "completionPoints=${entries.values.sumOf { it.completions.size.toLong() }} " +
            "boundaryLimitOffers=$boundaryLimitOffers boundaryLimitCuts=$boundaryLimitCuts " +
            "localBoundaryOffers=$localBoundaryOffers localBoundaryDrops=$localBoundaryDrops " +
            "prePublicationLocalOffers=$prePublicationLocalOffers prePublicationDeadLocals=$prePublicationDeadLocals " +
            "localMasks=${liveLocals?.retainedMasks ?: 0} localMaskWords=${liveLocals?.retainedWords ?: 0} " +
            "c2Queries=${queryCounts.c2Queries} c2Hits=${queryCounts.c2Hits} c2Native=${queryCounts.c2Native} c2Rows=${queryCounts.c2Rows} " +
            "c5Plans=${queryCounts.plans} c5PlanChecks=${queryCounts.planChecks} c5PlanHits=${queryCounts.planHits} c5PlanFallbacks=${queryCounts.planFallbacks} " +
            "oversizedPlanRequests=${queryCounts.oversizedPlanRequests} c5PreparedQueries=${queryCounts.c5PreparedQueries} " +
            "c5NativeQueries=${queryCounts.c5NativeQueries} c5ReferenceFallbacks=${queryCounts.c5ReferenceFallbacks} " +
            "emptyDataReplays=${queryCounts.emptyReplays} " +
            "offers=${counts.offers} bypasses=${counts.bypasses} scalars=${counts.scalarQueries} " +
            "observations=${counts.observations} trials=${counts.trials} drops=${counts.drops} " +
            "cuts=${counts.cuts} rawFallbacks=${counts.rawFallbacks} " +
            "certificates=${counts.certificates} certificateFallbacks=${counts.certificateFallbacks} budgetsSkipped=${counts.budgetsSkipped} " +
            (localMatchCounts?.diagnosticStatistics()?.plus(" ") ?: "") +
            (savedSelectionCounts?.diagnosticStatistics()?.plus(" ") ?: "") +
            "preparedExitEntries=${preparedExits.preparations} preparedExitTargetMasks=${preparedExits.targetMaskBuilds}" + gapDetails
    }

    /** Numeric-only snapshots at the owner barrier; no completion facts escape. */
    fun completionScalarStatistics(): Sequence<ScalarIdentityStatistics> = sequence {
        for (entry in entries.values) for (store in entry.completions.values) {
            store.scalarStatisticsSnapshot()?.let { yield(it) }
        }
    }

    fun forEachLocalInput(scope: BlockScope, visit: (LocalLink, Facts) -> Unit) {
        entries[scope]?.links?.forEachInput(visit)
    }
    /** Transfer every existing input directory, including saved-only entries. */
    fun detachJoinedLocalInputs(): Map<BlockScope, JoinedLocalInputs> {
        requireIdle()
        val acquired = LinkedHashMap<BlockScope, JoinedLocalInputs>()
        try {
            for ((scope, entry) in entries) {
                val moved = entry.links.detachJoinedInputs()
                try { acquired[scope] = moved } catch (error: Throwable) {
                    try { moved.close() } catch (cleanup: Throwable) { if (cleanup !== error) error.addSuppressed(cleanup) }
                    throw error
                }
            }
            return acquired
        } catch (error: Throwable) {
            for (moved in acquired.values) try { moved.close() } catch (cleanup: Throwable) {
                if (cleanup !== error) error.addSuppressed(cleanup)
            }
            throw error
        }
    }
    fun scopedSummaries(): Sequence<ScopedRunSummary> = sequence {
        for ((scope, e) in entries) if (scope != BlockScope.ROOT && e.stateOrNull != null)
            for ((exit, rows) in e.state.portSummaries.entries())
                yield(ScopedRunSummary(ScopedSummaryKey(key, scope, exit), rows))
    }
    fun scopedTargets(): Sequence<ScopedTargetRows> = entries.asSequence().filter { it.key != BlockScope.ROOT && it.value.stateOrNull != null }
        .map { (scope, e) -> ScopedTargetRows(key, scope, e.state.targets, methodExit) }
    fun scopedOutgoingTargets(): Sequence<ScopedTargetRows> = sequence {
        for ((scope, e) in entries) if (scope != BlockScope.ROOT && e.stateOrNull != null) {
            val byAddress = e.state.outgoingTargets.groupBy { row ->
                targetHandoffScope(scope, config.direction, e.borrowedExceptionalNormalZero, row)
            }
            for ((address, rows) in byAddress) yield(ScopedTargetRows(key, address, rows, methodExit))
        }
    }
    fun freezeChildren() {
        requireIdle()
        var failure: Throwable? = null
        fun release(action: () -> Unit) {
            try { action() } catch (error: Throwable) {
                val prior = failure
                if (prior == null) failure = error else if (prior !== error) prior.addSuppressed(error)
            }
        }
        try {
            for ((scope, e) in entries) if (scope != BlockScope.ROOT) e.stateOrNull?.let { state -> release { state.freeze() } }
            for (e in entries.values) release { e.links.clear() }
        } finally {
            entries.clear(); ready.clear(); pending.clear(); observers.clear(); preparedExits.clear(); released = true
        }
        failure?.let { throw it }
    }
}
