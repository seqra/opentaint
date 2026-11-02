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
        val links = BlockSummaryLinks(ops, mode, scope, ::onData, ::onTerminal, ::onRequest)
        fun addCompletion(child: BlockId, exit: PortId, original: PremiseKey, value: Facts): Facts? {
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
            return store.add(point, original, value)
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
        if (target in e.methodStarts && layout[e.scope.block].isLeaf)
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

    private fun savedRows(scope: BlockScope, actual: Facts): Sequence<Record> = sequence {
        val seen = HashSet<Record>()
        for (leaf in ops.leaves(actual)) {
            for (record in config.records.byEntry(key, scope, leaf))
                if (record.direction == config.direction && seen.add(record)) yield(record)
            for (record in config.records.byExit(key, scope, leaf))
                if (record.direction != config.direction && seen.add(record)) yield(record)
        }
    }

    private fun replaySaved(child: Entry, link: LocalLink, actual: Facts) {
        for (record in savedRows(child.scope, actual)) {
            val exit = checkNotNull(record.exitIn(config.direction))
            if (record.direction == config.direction) {
                for (scalar in annotatedLoopScalars(ops, record.conclusion)) {
                    val row = Record(key, record.direction, record.premise, scalar)
                    applySaved(child, link, actual, exit, record.premise, ops.leaves(scalar).single()) {
                        out -> application.applyRecord(actual, link.original, row, out)
                    }
                }
            } else {
                val seen = LinkedHashSet<Pair<RecordLeafView, Boolean>>()
                for (leaf in ops.leaves(actual)) record.forEachReversedAt(leaf) { view, protected ->
                    if (seen.add(view to protected)) applySavedView(child, link, actual, exit, view, protected)
                }
            }
        }
        for ((row, member) in config.normalTargets.candidates(key, child.scope, link.original, actual, mode))
            child.links.replaySavedTarget(link, actual, row, member)
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
        val grows = loopFieldLength(Pattern(view.result.fact, view.result.exclusion)) > loopFieldLength(view.premise)
        application.applyRecordView(actual, link.original, view, protected, object : LocalRelationOut {
            override fun data(original: PremiseKey, value: Facts) = onApplied(link, exit, grows, original, value)
            override fun target(original: PremiseKey, target: Target) = onTerminal(link, original, target)
            override fun markRequest(mark: TaintMark) = onRequest(link, actual, mark)
        })
    }

    private fun onData(link: LocalLink, exit: PortId, row: PremiseKey, geometry: Pattern,
                       original: PremiseKey, value: Facts) =
        onApplied(link, exit, loopSummaryGrows(row, geometry), original, value)

    private fun onApplied(link: LocalLink, exit: PortId, grows: Boolean, original: PremiseKey, value: Facts) {
        val parent = entries.getValue(link.parent)
        val child = layout[link.child.block]
        val completionExit = if (isEmptyBlock(child.id)) link.point else exit
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
                    restriction.restrict(config.run1, grows, bounded) { candidate -> observe(parent, child, link, exit, original, candidate) }
                for (kept in values) {
                    val fresh = parent.addCompletion(child.id, completionExit, original, kept) ?: continue
                    queue { routeCompleted(parent, child, link, exit, original, fresh) }
                }
            }
            override fun markRequest(mark: TaintMark) = error("A global local-boundary field limit cannot request a mark")
        })
    }

    private fun onTerminal(link: LocalLink, original: PremiseKey, target: Target) {
        queue { entries.getValue(link.parent).state.emitTarget(original, target) }
    }

    private fun routeCompleted(parent: Entry, child: MethodBlock, link: LocalLink, exit: PortId,
                               original: PremiseKey, value: Facts) {
        if (isEmptyBlock(child.id)) {
            if (link.point.ordinal >= 0) for (route in deliveryRoutes(link.point)) {
                if (route.feedbackLoop == parent.scope.block)
                    parent.state.retainBlockSummary(route.port, original, value)
                else if (layout.contains(parent.scope.block, route.to))
                    routeInside(parent, route.to, original, value, link.point, passedEmpty = true)
                else parent.state.retainBlockSummary(outputPort(route.port, parent.scope.block), original, value)
            } else for (target in entries.getValue(link.child).starts.toList()) {
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
        for (route in deliveryRoutes(exit)) {
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
        fun labelled(actual: Facts): Set<LoopLabelledAdmission> = buildSet {
            for ((scope, demand) in adjacentDemands) for (initial in demand.initials(actual, config.admissionPolicy))
                add(LoopLabelledAdmission(scope, LoopAdmissionFamily.ADJACENT, initial))
            for ((scope, demand) in repeatDemands) for (initial in demand.initials(actual, config.admissionPolicy))
                add(LoopLabelledAdmission(scope, LoopAdmissionFamily.REPEAT, initial))
        }
        val enclosingDemand = parent.demand
        val views = LoopConsumerViews(parent.scope, parent.rootEntry,
            { actual -> adjacentDemands.values.flatMap { it.initials(actual, config.admissionPolicy) }.toSet() },
            { actual -> repeatDemands.values.flatMap { it.initials(actual, config.admissionPolicy) }.toSet() },
            { actual -> adjacentScopes.asSequence().flatMap { scope -> savedRows(scope, actual) }
                .flatMap { record -> enclosingPorts(checkNotNull(record.exitIn(config.direction)), parent.scope.block)
                    .asSequence().map { LoopObservedRecord(record, it) } } },
            { pr, actual -> adjacentScopes.asSequence().flatMap { scope ->
                config.normalTargets.candidates(key, scope, pr, actual, mode).asSequence()
            }.map { (row, member) -> LoopObservedTarget(row, member, methodExit) } },
            { portId, pr, actual -> if (parent.rootEntry) checkNotNull(config.demand).intersect(key, pr, actual, config.admissionPolicy)
                else checkNotNull(enclosingDemand).intersect(portId, pr, actual, config.admissionPolicy) },
            { portId, pr -> if (parent.rootEntry) checkNotNull(config.demand).acceptsTarget(key, pr, config.admissionPolicy)
                else checkNotNull(enclosingDemand).acceptsTarget(portId, pr, config.admissionPolicy) },
            { pr, id -> config.normalTargets.contains(key, if (parent.rootEntry) null else parent.scope, pr, id) },
            port.shared.interpreter::isSummaryBase, ::labelled,
            { pr, actual -> if (parent.rootEntry) root.adjustObservedMethodExit(pr, actual) else actual })
        LoopConsumerObservation(ops, mode, views)
        }
        return observer.observe(original, value)
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
            "offers=${counts.offers} bypasses=${counts.bypasses} scalars=${counts.scalarQueries} " +
            "observations=${counts.observations} trials=${counts.trials} drops=${counts.drops} " +
            "cuts=${counts.cuts} rawFallbacks=${counts.rawFallbacks}" + gapDetails
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
            entries.clear(); ready.clear(); pending.clear(); observers.clear(); released = true
        }
        failure?.let { throw it }
    }
}
