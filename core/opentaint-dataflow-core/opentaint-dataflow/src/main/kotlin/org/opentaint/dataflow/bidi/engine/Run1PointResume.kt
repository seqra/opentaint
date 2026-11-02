package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.interp.*

/** Only immutable invocation state is retained, never a cached full call plan. */
data class CallResumeState(val callerLayer: Layer, val identityCandidate: Boolean? = null,
                           val pendingDemotion: Boolean = false)

data class OperationInput(val site: ResumeSite, val premise: PremiseKey, val facts: Facts,
                          val callState: CallResumeState? = null)

/** Actor-owned resume directory. Service replies name these rows; they never carry callbacks. */
internal class Run1PointResume(private val core: BlockRunState) {
    private data class PointKey(val site: ResumeSite, val initial: InitialAp, val base: AccessPathBase,
                                val tail: Tail, val fieldExclusion: ExclusionSet, val layer: Layer,
                                val state: CallResumeState?)
    private val pointKeys = HashMap<PointKey, Long>()
    private class PendingFlowImages(private var root: FlowNode) {
        fun addAll(incoming: FlowNode, ap: ApManager) {
            root = FlowAlgebra.mergeAdd(root, incoming, ap.cancellation)
        }
        fun snapshotRoot(): FlowNode = root
    }
    private class PointRow(val id: Long, val key: PointKey) {
        val pending = HashMap<TaintMark, PendingFlowImages>()
    }
    private data class DetachedAnswer(val group: TaintMark, val images: FlowNode)
    private val points = HashMap<Long, PointRow>()
    private data class ReadKey(val site: ResumeSite, val operation: StaticOperation)
    private val readKeys = HashMap<ReadKey, Long>()
    private val reads = HashMap<Long, Pair<OperationInput, StaticOperation>>()
    private data class WriterKey(val premise: PremiseKey, val output: Pattern, val layer: Layer)
    private val writerKeys = HashMap<WriterKey, Long>()
    private val writers = HashMap<Long, WriterKey>()
    private class DirectRow(val key: ReadKey, val payload: OperationInput, var waiting: MarkSet)
    private val direct = HashMap<Long, DirectRow>()
    private val directKeys = HashMap<ReadKey, Long>()
    private class WriterInput(val writer: WriterKey, var waiting: MarkSet)
    private val writerInputs = HashMap<Long, WriterInput>()
    private class ConditionalJoin(val writer: WriterKey) {
        val inputs = arrayOfNulls<RegionGroups>(writer.premise.size)
    }
    private data class JoinInput(val join: Long, val member: Int)
    private val conditionalKeys = HashMap<WriterKey, Long>()
    private val conditional = HashMap<Long, ConditionalJoin>()
    private val joinInputs = HashMap<Long, JoinInput>()
    private sealed interface CallResultKey {
        data class Ap(val output: Pattern, val layer: Layer) : CallResultKey
        data class Terminal(val target: Target) : CallResultKey
    }
    private data class CallKey(val callee: MethodKey, val ref: org.opentaint.dataflow.bidi.store.CallerRef,
                               val linkLayer: Layer, val premise: PremiseKey, val result: CallResultKey, val member: Int)
    private class CallContinuation(val key: CallKey, var part: Subscription, var result: StaticCallResult,
                                   val member: Int) { var waiting = MarkSet.EMPTY }
    private val callKeys = HashMap<CallKey, Long>()
    private val calls = HashMap<Long, CallContinuation>()

    fun callInterest(part: Subscription, result: StaticCallResult, member: Int) {
        if (!RuntimeDataDomain.packet(part.ref.premise, part.added) || !RuntimeDataDomain.premise(result.premise)) return
        val initial = result.premise.member(member)
        val atom = (initial.mark as? MarkSlot.Concrete)?.mark ?: return
        val statistics = core.context.shared.n2Statistics
        val pieces = when (result) {
            is StaticCallResult.Ap -> {
                val pub = result.publication
                if (!RuntimeDataDomain.packet(pub.premise, pub.conclusion)) return
                core.ops.leaves(pub.conclusion).map { leaf ->
                    val plain = core.ap.factsOf(leaf.fact, leaf.exclusion, pub.layer)
                    val conclusion = if (plain is TaintTree && pub.conclusion is TaintTree)
                        plain.withProtection(pub.conclusion.nonSubsumable) else plain
                    CallResultKey.Ap(leaf, pub.layer) to StaticCallResult.Ap(pub.copy(conclusion = conclusion))
                }.toList()
            }
            is StaticCallResult.Terminal -> listOf(CallResultKey.Terminal(result.summary.target) to result)
        }
        for ((resultKey, piece) in pieces) {
            statistics?.staticGroupCallOffered()
            val key = CallKey(part.callee, part.ref, part.linkLayer, result.premise, resultKey, member)
            val id = callKeys.getOrPut(key) {
                (core.nextStaticTicket()).also { calls[it] = CallContinuation(key, part, piece, member) }
            }
            val row = calls.getValue(id)
            // AP equality retains the current per-leaf key and protection refresh.
            val previous = row.result
            if (previous is StaticCallResult.Ap && piece is StaticCallResult.Ap)
                row.result = StaticCallResult.Ap(previous.publication.copy(conclusion =
                    core.ap.mergeAddDelta(previous.publication.conclusion, piece.publication.conclusion).first))
            row.part = row.part.copy(added = core.ap.mergeAddDelta(row.part.added, part.added).first)
            val fresh = MarkSet.of(core.ap.marks.runtimeAtom(atom, core.mode.markMode)) - row.waiting
            if (fresh.isEmpty) continue
            statistics?.staticGroupCallFallbackAdmitted()
            row.waiting += fresh
            core.staticBatch.interests += StaticInterest(core.key, id, initial.toPattern(), fresh)
        }
        core.requestWork()
    }

    fun reached(summary: StatementSummary, at: OperationInput) {
        if (!RuntimeDataDomain.packet(at.premise, at.facts)) return
        if (at.facts !is Reach || !at.premise.isZero) return
        for (operation in summary.staticOperations) {
            if (core.config.disableRun1Statics && when (operation) {
                    is StaticOperation.Read -> true
                    is StaticOperation.Write -> core.dropsStaticField(operation.target.fact)
                    is StaticOperation.MarkInput -> operation.position.fact.path.size != 1 ||
                        (operation.position.fact.tail != Tail.EXACT && !operation.includeBase)
                }) continue
            val key = ReadKey(at.site, operation)
            val id = readKeys.getOrPut(key) {
                (core.nextStaticTicket()).also { reads[it] = at to operation }
            }
            when (operation) {
                is StaticOperation.Read -> core.staticBatch.reads += StaticReadRegistration(core.key, id,
                    Pattern(operation.transfer.from, operation.transfer.exclusion))
                is StaticOperation.MarkInput -> {
                    val mark = (operation.position.fact.mark as? MarkSlot.Concrete)?.mark ?: continue
                    val groups = MarkSet.of(core.ap.marks.runtimeAtom(mark, core.mode.markMode))
                    if (operation.position.fact.path.size == 1) {
                        val exact = operation.position.fact.tail == Tail.EXACT
                        // A wildcard is a field-query descriptor, never a class
                        // FLOW initial. Its empty-suffix branch is an exact
                        // global marker; BELOW cleaners omit that branch.
                        if (!exact && !core.config.disableRun1Statics)
                            core.staticBatch.reads += StaticReadRegistration(core.key, id, operation.position)
                        if (exact || operation.includeBase) {
                            val directId = directKeys.getOrPut(key) {
                                (core.nextStaticTicket()).also { direct[it] = DirectRow(key, at, MarkSet.EMPTY) }
                            }
                            val row = direct.getValue(directId)
                            val fresh = groups - row.waiting
                            if (!fresh.isEmpty) {
                                row.waiting += fresh
                                val point = operation.position.copy(fact = operation.position.fact.copy(tail = Tail.EXACT),
                                    exclusion = ExclusionSet.Empty)
                                core.staticBatch.interests += StaticInterest(core.key, directId, point, fresh)
                            }
                        }
                    } else core.staticBatch.reads += StaticReadRegistration(core.key, id, operation.position)
                }
                is StaticOperation.Write -> Unit
            }
        }
    }

    fun request(at: OperationInput, groups: MarkSet) {
        if (!RuntimeDataDomain.packet(at.premise, at.facts)) return
        val original = at.premise as? InitialAp ?: return
        val flow = at.facts as? FlowTree ?: return
        if (original.base != STATIC || original.mark !is MarkSlot.Star) return
        if (groups.isEmpty) return
        val key = PointKey(at.site, original, flow.base, flow.tail, flow.exclusion, flow.layer, at.callState)
        val id = pointKeys.getOrPut(key) {
            (core.nextStaticTicket()).also { points[it] = PointRow(it, key) }
        }
        val row = points.getValue(id)
        var subscribe = MarkSet.EMPTY
        groups.forEach { group ->
            core.ap.cancellation.checkpoint()
            val images = row.pending[group]
            if (images == null) {
                row.pending[group] = PendingFlowImages(flow.root)
                subscribe += group
            } else images.addAll(flow.root, core.ap)
        }
        if (!subscribe.isEmpty) {
            core.staticBatch.interests += StaticInterest(core.key, id, original.toPattern(), subscribe)
        }
        core.requestWork()
    }

    /** Only an executed local producer reaches this boundary. Its bounded
     * scalar relation belongs to the writer, independently of summary deltas. */
    fun localWrite(premise: PremiseKey, value: Facts) {
        if (!RuntimeDataDomain.packet(premise, value)) return
        check(value.base == STATIC)
        // A completed local write already has its permitted concrete input.
        // Supply the actual bounded output here, independently of outgoing exit
        // rules or summary publication. FLOW writers remain registered below.
        if (value is TaintTree) core.staticBatch.supplies += core.staticSlices(value)
        for (leaf in core.ops.leaves(value)) {
            if (leaf.fact.path.size < 2) continue // exact class markers have no FLOW writer
            val region = Run1StaticService.region(leaf)
            core.staticBatch.writes += region
            if (value !is FlowTree) continue
            check(premise is InitialAp && !premise.isZero && premise.mark is MarkSlot.Star)
            val key = WriterKey(premise, leaf, value.layer)
            if (key in writerKeys) continue
            val id = core.nextStaticTicket()
            writerKeys[key] = id
            writers[id] = key
            if (premise.base == STATIC)
                core.staticBatch.writers += StaticWriterRegistration(core.key, id, premise, region)
            else core.staticBatch.flowWriters += StaticFlowWriter(core.key, id, region)
        }
        core.requestWork()
    }

    /** A computed result can supply the pool before its summary is erased.
     * Promotion never admits a new write point or FLOW writer. */
    fun computedGroups(premise: PremiseKey, value: Facts) {
        if (!RuntimeDataDomain.packet(premise, value)) return
        check(value.base == STATIC)
        if (value !is TaintTree) return
        if (core.hasKnownStaticGroupInput(premise)) {
            val initial = premise as InitialAp
            val actual = core.knownStaticInput(initial)
            for (leaf in core.ops.leaves(value)) {
                core.ap.cancellation.checkpoint()
                core.context.shared.n2Statistics?.staticGroupSupplyDirect()
                val scalar = core.ap.factsOf(leaf.fact, leaf.exclusion, value.layer)
                core.composeStaticSummaryWithActualInput(initial, scalar, actual) { value ->
                    core.staticBatch.supplies += core.staticSlices(value)
                }
            }
        } else if (!premise.isZero && (0 until premise.size).all { premise.member(it).base == STATIC }) {
            for (leaf in core.ops.leaves(value)) {
                core.context.shared.n2Statistics?.staticGroupJoinFallback()
                val key = WriterKey(premise, leaf, value.layer)
                if (key in conditionalKeys) continue
                // A fixed-group conditional is a pending complete binding, not a
                // permanent summary archive or a service-side Cartesian join.
                // Its immutable scalar survives erasure of the method row.
                val joinId = core.nextStaticTicket()
                conditionalKeys[key] = joinId
                conditional[joinId] = ConditionalJoin(key)
                repeat(premise.size) { member ->
                    val initial = premise.member(member)
                    val atom = (initial.mark as MarkSlot.Concrete).mark
                    val inputId = core.nextStaticTicket()
                    joinInputs[inputId] = JoinInput(joinId, member)
                    core.staticBatch.interests += StaticInterest(core.key, inputId, initial.toPattern(),
                        MarkSet.of(core.ap.marks.runtimeAtom(atom, core.mode.markMode)))
                }
            }
        }
        if (premise.isZero)
            core.staticBatch.supplies += core.staticSlices(value)
        core.requestWork()
    }

    fun onEffect(effect: StaticOwnerEffect) {
        when (effect) {
            is StaticOwnerEffect.ReadReady -> {
                val (at, operation) = checkNotNull(reads[effect.id]) { "Unknown static read reply" }
                val position = effect.region.fact.path
                if (position.size < 2) return // class-point MarkInput uses the direct group path
                val initial = core.ap.initial(Pattern(PathFact(STATIC, position.take(2), Tail.STAR, MarkSlot.STAR), ExclusionSet.Empty))
                val input = core.ap.factsOf(effect.region.fact.copy(mark = MarkSlot.STAR,
                    tail = if (effect.region.fact.tail == Tail.EXACT || effect.region.fact.tail == Tail.ANY_TAINT) Tail.STAR else effect.region.fact.tail),
                    ExclusionSet.Empty, Layer.DEMAND)
                core.installPoint(initial, input, at.site, at.callState)
            }
            is StaticOwnerEffect.PointReady -> {
                calls[effect.id]?.let { call ->
                    call.waiting -= effect.supply.groups
                    if (call.waiting.isEmpty) { callKeys.remove(call.key); calls.remove(effect.id) }
                    core.staticCallSupply(call.part, call.result, call.member, effect.supply)
                    return
                }
                writerInputs[effect.id]?.let { input ->
                    input.waiting -= effect.supply.groups
                    if (input.waiting.isEmpty) writerInputs.remove(effect.id)
                    publishMatched(input.writer, listOf(effect.supply))
                    core.requestWork()
                    return
                }
                joinInputs.remove(effect.id)?.let { input ->
                    val join = conditional.getValue(input.join)
                    join.inputs[input.member] = effect.supply
                    if (join.inputs.all { it != null }) {
                        conditional.remove(input.join)
                        check(conditionalKeys.remove(join.writer) == input.join)
                        publishMatched(join.writer, join.inputs.map { checkNotNull(it) })
                    }
                    core.requestWork()
                    return
                }
                val directRow = direct[effect.id]
                if (directRow != null) {
                    val at = directRow.payload
                    directRow.waiting -= effect.supply.groups
                    if (directRow.waiting.isEmpty) { directKeys.remove(directRow.key); direct.remove(effect.id) }
                    val actual = core.staticFacts(effect.supply)
                    for (leaf in core.ops.leaves(actual)) {
                        val premise = concreteInitial(leaf)
                        core.installPoint(premise, core.ops.startFact(premise, core.mode), at.site, at.callState)
                    }
                    return
                }
                answerPackedPoint(effect)
            }
            is StaticOwnerEffect.WriterInterest -> {
                val writer = checkNotNull(writers[effect.id]) { "Unknown static writer interest" }
                val original = writer.premise as? InitialAp ?: return
                check(!original.isZero && original.mark is MarkSlot.Star && writer.output.fact.mark is MarkSlot.Star)
                if (original.base == STATIC) {
                    val inputId = core.nextStaticTicket()
                    writerInputs[inputId] = WriterInput(writer, effect.groups)
                    core.staticBatch.interests += StaticInterest(core.key, inputId, original.toPattern(), effect.groups)
                } else {
                    for (atom in effect.groups.ids)
                        core.addMarkRequest(original, TaintMark(atom))
                }
            }
        }
        core.requestWork()
    }

    private fun answerPackedPoint(effect: StaticOwnerEffect.PointReady) {
        val row = checkNotNull(points[effect.id]) { "Unknown static point reply" }
        effect.supply.groups.forEach { group -> check(row.pending.containsKey(group)) }
        val detached = ArrayList<DetachedAnswer>()
        effect.supply.groups.forEach { group ->
            detached += DetachedAnswer(group, checkNotNull(row.pending.remove(group)).snapshotRoot())
        }
        // Detach every supplied group before any callback. Later requests must
        // subscribe again; an immutable detached root cannot acquire new images.
        if (row.pending.isEmpty()) {
            check(pointKeys.remove(row.key) == row.id)
            check(points.remove(row.id) === row)
        }
        for (answer in detached) {
            core.ap.cancellation.checkpoint()
            materializeScalarImages(row.key, answer.images,
                RegionGroups(effect.supply.region, MarkSet.of(answer.group)))
        }
    }

    private fun materializeScalarImages(key: PointKey, images: FlowNode, supply: RegionGroups) {
        val actual = core.staticFacts(supply)
        for (leaf in core.ops.leaves(actual)) {
            core.ap.cancellation.checkpoint()
            val premise = concreteInitial(leaf)
            materializeStaticFlowImages(core.ops, core.mode, key.initial, premise, images,
                key.base, key.tail, key.fieldExclusion, key.layer) { value ->
                core.installPoint(premise, value, key.site, key.state)
            }
        }
    }

    private fun publishMatched(writer: WriterKey, inputs: List<RegionGroups>) {
        // Both FLOW writers and unanswered fixed-mark input joins own the
        // admitted bounded scalar; neither borrows an erased method summary.
        val current = core.ap.factsOf(writer.output.fact, writer.output.exclusion, writer.layer)
        core.composeStaticSummary(writer.premise, current, inputs) { value ->
            core.staticBatch.supplies += core.staticSlices(value)
        }
    }

    private fun concreteInitial(leaf: Pattern): InitialAp = concreteStaticResumeInitial(core.ap, leaf)

    fun clear() { pointKeys.clear(); points.clear(); readKeys.clear(); reads.clear(); writerKeys.clear(); writers.clear(); direct.clear(); directKeys.clear(); callKeys.clear(); calls.clear(); writerInputs.clear(); conditionalKeys.clear(); conditional.clear(); joinInputs.clear() }
}
