package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId

private typealias Input = LocalInputValue
private typealias InputKey = LocalInputKey

/** Optional numeric census shared by one method's block links. No input or result history. */
internal class LocalSummaryMatchStatistics {
    var offers = 0L; internal set
    var freshInputGroups = 0L; internal set
    var freshInputDeltas = 0L; internal set
    var publicationRows = 0L; internal set
    var targetRows = 0L; internal set
    var candidatePairs = 0L; internal set
    var publicationCandidatePairs = 0L; internal set
    var publicationLinearPairBound = 0L; internal set
    var nativeMatches = 0L; internal set
    var ndCombinations = 0L; internal set
    var dataCallbacks = 0L; internal set
    var targetCallbacks = 0L; internal set

    fun diagnosticStatistics(): String =
        "localInputOffers=$offers localFreshInputGroups=$freshInputGroups localFreshInputDeltas=$freshInputDeltas " +
        "localPublishedRows=$publicationRows localPublishedTargetRows=$targetRows " +
        "localCandidatePairs=$candidatePairs localPublicationCandidatePairs=$publicationCandidatePairs " +
        "localPublicationLinearPairs=$publicationLinearPairBound " +
        "localNativeMatches=$nativeMatches localNdCombinations=$ndCombinations " +
        "localDataCallbacks=$dataCallbacks localTargetCallbacks=$targetCallbacks"
}

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
    private val matchStatistics: LocalSummaryMatchStatistics? = null,
) {
    private val ap get() = ops.manager
    private val application = LocalRelationApplication(ops, mode)
    private var inputDirectory: LocalInputDirectory? = LocalInputDirectory(ops)
    private val inputs: LocalInputDirectory get() = checkNotNull(inputDirectory) { "Local links are sealed" }
    private fun checkLive() { checkNotNull(inputDirectory) { "Local links are sealed" } }
    private val publications = LinkedHashMap<PortId, PublicationIndex>()
    private var targets = PublicationIndex(ap, ops)
    private val deliveries = ArrayDeque<Delivery>()
    private sealed interface Delivery {
        data class Data(val input: Input, val exit: PortId, val row: Publication, val member: Int,
                        val matched: Facts) : Delivery
        data class Terminal(val input: Input, val row: TargetSummary, val member: Int, val saved: Boolean) : Delivery
    }
    private data class NdKey(val parent: BlockScope, val point: PortId, val exit: PortId,
                             val premise: PremiseSet, val layer: Layer)
    private data class NdInput(val link: LocalLink, val initial: InitialAp, val layer: Layer, val protected: Boolean) {
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
        matchStatistics?.let { it.offers++ }
        require(link.child == scope)
        ap.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(link.original, actual)) return
        require(actual.layer == link.layer)
        val key = InputKey(link, actual.groupKey)
        val old = inputs[key]
        val fresh = if (old == null) {
            matchStatistics?.let { it.freshInputGroups++ }
            inputs[key] = Input(link, actual)
            actual
        } else {
            val (merged, delta) = ap.mergeAddDelta(old.value, actual)
            if (delta == null) return
            old.value = merged
            delta
        }
        matchStatistics?.let { it.freshInputDeltas++ }
        inputs.recordDelta(key, fresh)
        // Deliver the fresh packet only. The standing row retains the current union.
        val offered = Input(link, fresh)
        val matches = HashMap<InitialAp, MatchedInput?>()
        for ((exit, index) in publications) {
            for ((row, member) in index.candidates(link.original, fresh, mode))
                queueData(offered, exit, row, member, matches)
            if (isStaticControl(offered)) for ((row, member) in index.staticCandidates())
                queueData(offered, exit, row, member, matches)
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
        matchStatistics?.let { stats ->
            stats.publicationRows += fresh.size
            for (row in fresh) stats.publicationLinearPairBound += inputs.size.toLong() * row.premise.size
        }
        // Snapshot before delivery. A callback can offer another local input.
        val matches = HashMap<InputKey, MutableMap<InitialAp, MatchedInput?>>()
        for (row in fresh) for ((input, member) in inputs.candidates(row.premise, mode)) {
            matchStatistics?.let { it.publicationCandidatePairs++ }
            val cache = matches.getOrPut(InputKey(input.link, input.value.groupKey)) { HashMap() }
            queueData(input, exit, row, member, cache)
        }
    }

    fun publishTargets(rows: TargetBatch) {
        checkLive()
        val fresh = targets.addTargets(rows)
        matchStatistics?.let { stats ->
            stats.targetRows += fresh.size
        }
        for (row in fresh) for ((input, member) in inputs.candidates(row.premise, mode)) {
            ap.cancellation.checkpoint()
            if (isStaticControl(input) && row.premise.member(member).base == STATIC ||
                application.targetArmLayer(input.value, row.premise.member(member), row.target,
                    saved = false, offeredLayer = input.link.layer) != null)
                deliveries += Delivery.Terminal(input, row, member, saved = false)
        }
    }

    /** The certified static lane changes the selected original as well as the packet.
     * Keep the raw selected packet for ordinary request callbacks. */
    private data class MatchedInput(val input: Input, val facts: Facts)
    private fun queueData(offered: Input, exit: PortId, row: Publication, member: Int,
                          cache: MutableMap<InitialAp, MatchedInput?>) {
        matchStatistics?.let { it.candidatePairs++ }
        val initial = row.premise.member(member)
        if (!cache.containsKey(initial)) {
            val input = if (isStaticControl(offered) && initial.base == STATIC)
                suppliedStaticInput(offered, initial) else offered
            matchStatistics?.let { it.nativeMatches++ }
            cache[initial] = ops.satisfying(input.value, initial, mode)?.let { MatchedInput(input, it) }
        }
        val matched = cache[initial] ?: return
        deliveries += Delivery.Data(matched.input, exit, row, member, matched.facts)
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
        override fun data(original: PremiseKey, value: Facts) {
            matchStatistics?.let { it.dataCallbacks++ }
            data(input.link, exit, row, geometry, original, value)
        }
        override fun target(original: PremiseKey, target: Target) {
            matchStatistics?.let { it.targetCallbacks++ }
            terminal(input.link, original, target)
        }
        override fun markRequest(mark: TaintMark) = request(input.link, input.value, mark)
    }

    private fun deliver(delivery: Delivery.Data) {
        val (input, exit, row, member, matchedInput) = delivery
        // A different geometry has a different loop growth classification.
        for (scalar in annotatedLoopScalars(ops, row.conclusion)) {
            val geometry = ops.leaves(scalar).single()
            when (val premise = row.premise) {
                is InitialAp -> application.applyMatched(matchedInput, input.link.original, premise, scalar,
                    output(input, exit, premise, geometry))
                is PremiseSet -> {
                    check(!mode.run1 && mode.direction == Direction.FORWARD)
                    val matched = matchedInput as? TaintTree ?: continue
                    val key = NdKey(input.link.parent, input.link.point, exit, premise, scalar.layer)
                    val join = joins.getOrPut(key) { NdSummaryJoin(ap, premise.size) }
                    val binding = NdInput(input.link, premise.member(member), matched.layer, matched.nonSubsumable != null).also { it.matched = matched }
                    fun emit(parts: List<NdInput>, value: TaintTree) {
                        matchStatistics?.let { it.ndCombinations++ }
                        var original: PremiseKey = ap.zero
                        for (part in parts) original = ap.union(original, part.link.original)
                        val complete = Input(input.link.copy(original = original), input.value)
                        for (piece in annotatedLoopScalars(ops, value))
                            application.applyCombination(parts.map { LocalRelationBinding(it.link.original, it.initial, it.matched) },
                                piece as TaintTree, output(complete, exit, premise, ops.leaves(piece).single()))
                    }
                    // The key fixes the literal, origin, support and class. The
                    // matched geometry is only a validity witness for this full join.
                    for ((parts, value) in join.addSubscription(member, binding)) emit(parts, value)
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
            if (row.target !is Target.NormalTarget || parts.all { it.layer == Layer.NORMAL }) {
                matchStatistics?.let { it.targetCallbacks++ }
                terminal(input.link, original, row.target)
            }
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
        owned.releaseCandidateIndex()
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
