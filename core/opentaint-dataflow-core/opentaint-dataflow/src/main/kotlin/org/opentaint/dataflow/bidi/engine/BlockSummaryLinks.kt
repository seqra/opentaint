package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId

private typealias Input = LocalInputValue
private typealias InputKey = LocalInputKey

/** A local boundary has no call instruction, binding stages, or iteration counter. */
internal data class LocalLink(
    val parent: BlockScope,
    val point: PortId,
    val original: PremiseKey,
    val layer: Layer,
    val child: BlockScope,
)

/** Exact live inputs and admitted current publications for one child entry.
 * Saved records are replayed separately on every complete offer before this store is used.
 * All callbacks are queued under the original method's work reservation.
 */
internal class BlockSummaryLinks(
    private val ops: ApOps,
    private val mode: ApMode,
    val scope: BlockScope,
    private val data: (LocalLink, PortId, PremiseKey, Pattern, PremiseKey, Facts) -> Unit,
    private val terminal: (LocalLink, PremiseKey, Target) -> Unit,
    private val request: (LocalLink, Facts, TaintMark) -> Unit,
) {
    private val ap get() = ops.manager
    private val application = LocalRelationApplication(ops, mode)
    private var inputDirectory: LocalInputDirectory? = LocalInputDirectory()
    private val inputs: LocalInputDirectory get() = checkNotNull(inputDirectory) { "Local links are sealed" }
    private fun checkLive() { checkNotNull(inputDirectory) { "Local links are sealed" } }
    private val publications = LinkedHashMap<PortId, PublicationIndex>()
    private var targets = PublicationIndex(ap, ops)
    private val deliveries = ArrayDeque<Delivery>()
    private sealed interface Delivery {
        data class Data(val input: Input, val exit: PortId, val row: Publication, val member: Int) : Delivery
        data class Terminal(val input: Input, val row: TargetSummary, val member: Int, val saved: Boolean) : Delivery
    }
    private data class NdKey(val parent: BlockScope, val point: PortId, val exit: PortId,
                             val premise: PremiseSet, val layer: Layer)
    private data class NdInput(val link: LocalLink, val initial: InitialAp, val layer: Layer) {
        lateinit var matched: TaintTree
    }
    private val joins = HashMap<NdKey, NdSummaryJoin<NdInput>>()
    private data class TerminalKey(val parent: BlockScope, val point: PortId, val premise: PremiseSet,
                                   val target: Target, val saved: Boolean)
    private data class TerminalInput(val link: LocalLink, val layer: Layer)
    private val terminalJoins = HashMap<TerminalKey, KaryJoin<TerminalInput>>()

    val hasPending: Boolean get() = deliveries.isNotEmpty()
    val inputGroups: Int get() = inputs.size

    fun offer(link: LocalLink, actual: Facts) {
        checkLive()
        require(link.child == scope)
        ap.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(link.original, actual)) return
        require(actual.layer == link.layer)
        val key = InputKey(link, actual.groupKey)
        val old = inputs[key]
        val fresh = if (old == null) {
            inputs[key] = Input(link, actual)
            actual
        } else {
            val (merged, delta) = ap.mergeAddDelta(old.value, actual)
            if (delta == null) return
            old.value = merged
            delta
        }
        // Deliver the fresh packet only. The standing row retains the current union.
        val offered = Input(link, fresh)
        for ((exit, index) in publications) {
            for ((row, member) in index.candidates(link.original, fresh, mode))
                deliveries += Delivery.Data(offered, exit, row, member)
            if (isStaticControl(offered)) for ((row, member) in index.staticCandidates())
                deliveries += Delivery.Data(offered, exit, row, member)
        }
        for ((row, member) in targets.targetCandidates(link.original, fresh, mode))
            deliveries += Delivery.Terminal(offered, row, member, saved = false)
        if (isStaticControl(offered)) for ((row, member) in targets.staticTargetCandidates())
            deliveries += Delivery.Terminal(offered, row, member, saved = false)
    }

    fun publish(exit: PortId, rows: List<Publication>) {
        checkLive()
        val index = publications.getOrPut(exit) { PublicationIndex(ap, ops, flowBacked = true) }
        val fresh = index.addAll(rows)
        // Snapshot before delivery. A callback can offer another local input.
        val current = inputs.values.map { Input(it.link, it.value) }
        for (row in fresh) for (input in current) for (member in 0 until row.premise.size) {
            ap.cancellation.checkpoint()
            if (isStaticControl(input) && row.premise.member(member).base == STATIC ||
                ops.satisfying(input.value, row.premise.member(member), mode) != null)
                deliveries += Delivery.Data(input, exit, row, member)
        }
    }

    fun publishTargets(rows: TargetBatch) {
        checkLive()
        val fresh = targets.addTargets(rows)
        val current = inputs.values.map { Input(it.link, it.value) }
        for (row in fresh) for (input in current) for (member in 0 until row.premise.size) {
            ap.cancellation.checkpoint()
            if (isStaticControl(input) && row.premise.member(member).base == STATIC ||
                application.targetArmLayer(input.value, row.premise.member(member), row.target,
                    saved = false, offeredLayer = input.link.layer) != null)
                deliveries += Delivery.Terminal(input, row, member, saved = false)
        }
    }

    fun replaySavedTarget(link: LocalLink, actual: Facts, row: TargetSummary, member: Int) {
        checkLive()
        if (row.premise.isZero && row.target is Target.NormalTarget) return
        deliveries += Delivery.Terminal(Input(link, actual), row, member, saved = true)
    }

    /** Bounded draining makes every local callback visible to the method idle test. */
    fun drain(quantum: Int): Int {
        checkLive()
        require(quantum > 0)
        var done = 0
        while (done < quantum && deliveries.isNotEmpty()) {
            ap.cancellation.checkpoint()
            when (val next = deliveries.removeFirst()) {
                is Delivery.Data -> deliver(next)
                is Delivery.Terminal -> deliverTarget(next)
            }
            done++
        }
        return done
    }

    private fun output(input: Input, exit: PortId, row: PremiseKey, geometry: Pattern) = object : LocalRelationOut {
        override fun data(original: PremiseKey, value: Facts) =
            data(input.link, exit, row, geometry, original, value)
        override fun target(original: PremiseKey, target: Target) = terminal(input.link, original, target)
        override fun markRequest(mark: TaintMark) = request(input.link, input.value, mark)
    }

    private fun deliver(delivery: Delivery.Data) {
        val (offered, exit, row, member) = delivery
        val input = if (isStaticControl(offered) && row.premise.member(member).base == STATIC)
            suppliedStaticInput(offered, row.premise.member(member)) else offered
        // A different geometry has a different loop growth classification.
        for (scalar in annotatedLoopScalars(ops, row.conclusion)) {
            val geometry = ops.leaves(scalar).single()
            when (val premise = row.premise) {
                is InitialAp -> application.applyCurrent(input.value, input.link.original, premise, scalar,
                    output(input, exit, premise, geometry))
                is PremiseSet -> {
                    check(!mode.run1 && mode.direction == Direction.FORWARD)
                    val matched = ops.satisfying(input.value, premise.member(member), mode) as? TaintTree ?: continue
                    val key = NdKey(input.link.parent, input.link.point, exit, premise, scalar.layer)
                    val join = joins.getOrPut(key) { NdSummaryJoin(ap, premise.size) }
                    val binding = NdInput(input.link, premise.member(member), matched.layer).also { it.matched = matched }
                    fun emit(parts: List<NdInput>, value: TaintTree) {
                        var original: PremiseKey = ap.zero
                        for (part in parts) original = ap.union(original, part.link.original)
                        val complete = Input(input.link.copy(original = original), input.value)
                        for (piece in annotatedLoopScalars(ops, value))
                            application.applyCombination(parts.map { LocalRelationBinding(it.link.original, it.initial, it.matched) },
                                piece as TaintTree, output(complete, exit, premise, ops.leaves(piece).single()))
                    }
                    for ((parts, value) in join.addSubscription(member, binding) { prior, offered ->
                        val (merged, delta) = ap.mergeAddDelta(prior.matched, offered.matched)
                        prior.matched = merged as TaintTree
                        delta != null
                    }) emit(parts, value)
                    for ((parts, value) in join.addConclusion(scalar as TaintTree)) emit(parts, value)
                }
            }
        }
    }

    private fun deliverTarget(delivery: Delivery.Terminal) {
        val (offered, row, member, saved) = delivery
        val input = if (isStaticControl(offered) && row.premise.member(member).base == STATIC)
            suppliedStaticInput(offered, row.premise.member(member)) else offered
        val layer = application.targetArmLayer(input.value, row.premise.member(member), row.target,
            saved, input.link.layer) ?: return
        val binding = TerminalInput(input.link, layer)
        val combinations = when (val premise = row.premise) {
            is InitialAp -> listOf(listOf(binding))
            is PremiseSet -> terminalJoins.getOrPut(
                TerminalKey(input.link.parent, input.link.point, premise, row.target, saved)
            ) { KaryJoin(premise.size, ap.cancellation) }.add(member, binding)
        }
        for (parts in combinations) {
            var original: PremiseKey = ap.zero
            for (part in parts) original = ap.union(original, part.link.original)
            if (row.target !is Target.NormalTarget || parts.all { it.layer == Layer.NORMAL })
                terminal(input.link, original, row.target)
        }
    }

    private fun isStaticControl(input: Input): Boolean =
        mode.run1 && input.link.original.isZero && input.value is Reach

    /**
     * Reuse the run-1 static summary lane. The physical read has already received
     * this exact/static-field input from the pool before it can publish its row.
     * Replaying that certified original through a local ZERO continuation needs
     * no new read, mark interest, writer registration or pool supply.
     */
    private fun suppliedStaticInput(input: Input, initial: InitialAp): Input {
        validateRun1Initial(initial, mode.fieldLimit)
        check(initial.base == STATIC && initial.pathData.size in 1..2)
        val actual = ops.startFact(initial, mode).withLayer(Layer.DEMAND)
        return Input(input.link.copy(original = initial, layer = Layer.DEMAND), actual)
    }

    fun forEachInput(visit: (LocalLink, Facts) -> Unit) {
        checkLive()
        val snapshot = inputs.values.map { it.link to it.value }
        for ((link, value) in snapshot) { ap.cancellation.checkpoint(); visit(link, value) }
    }

    internal fun detachJoinedInputs(): JoinedLocalInputs {
        check(deliveries.isEmpty()) { "Local deliveries must drain before input detach" }
        val owned = checkNotNull(inputDirectory) { "Local inputs were already detached" }
        inputDirectory = null
        return JoinedLocalInputs(owned)
    }

    fun clear() {
        check(deliveries.isEmpty()) { "Local deliveries must drain before release" }
        inputDirectory?.clear()
        inputDirectory = null
        publications.clear(); joins.clear(); terminalJoins.clear()
        targets = PublicationIndex(ap, ops)
    }
}
