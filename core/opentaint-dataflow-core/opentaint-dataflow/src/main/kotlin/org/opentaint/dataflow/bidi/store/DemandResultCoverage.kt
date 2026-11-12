package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*
import java.util.ArrayDeque
import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.atomic.AtomicLongArray

internal enum class PreparedPlanFallback {
    RUN, STATIC_COMPLETION, SHARED_CARRY, EMPTY_TEMPLATES, OVERSIZE_TEMPLATES, ZERO_TEMPLATE, OCCURRENCE_BUDGET,
}

/** Counters only. A query never retains its path trace in the frozen snapshot. */
internal class DemandQueryStatistics : DemandScalarWork {
    private val values = AtomicLongArray(18)
    private val admissions = AtomicLongArray(16 * 5)
    private val restriction = AtomicLongArray(11)
    private val depths = AtomicLongArray(5 * 17)
    private val sampleOrdinal = AtomicLong()
    private val rowSamples = ArrayDeque<String>()
    private val prepared = AtomicLongArray(12)
    private val tries = AtomicLongArray(3)
    private val preparedFallbacks = AtomicLongArray(PreparedPlanFallback.entries.size)
    fun add(kind: Int, amount: Long = 1) { values.addAndGet(kind, amount) }
    fun preparedPlan(checked: Int, accepted: Int, programs: Int) {
        prepared.incrementAndGet(0)
        prepared.addAndGet(1, checked.toLong())
        prepared.addAndGet(2, accepted.toLong())
        prepared.addAndGet(3, programs.toLong())
    }
    fun preparedQuery() { prepared.incrementAndGet(4) }
    fun preparedFallback(reason: PreparedPlanFallback) { preparedFallbacks.incrementAndGet(reason.ordinal) }
    override fun stream() { prepared.incrementAndGet(5) }
    override fun scalar() { prepared.incrementAndGet(6) }
    override fun candidate() { prepared.incrementAndGet(7) }
    override fun selectedReference(size: Int) {
        prepared.incrementAndGet(8)
        var old = prepared[9]
        while (size > old && !prepared.compareAndSet(9, old, size.toLong())) old = prepared[9]
    }
    override fun overflow() { prepared.incrementAndGet(10) }
    override fun pack() { prepared.incrementAndGet(11) }
    /** Aggregate once per trie query; disabled diagnostics perform no counter updates. */
    fun trieQuery(nodes: Long, profiles: Long, candidates: Long) {
        tries.addAndGet(0, nodes)
        tries.addAndGet(1, profiles)
        tries.addAndGet(2, candidates)
    }
    fun admission(entry: Pattern, actual: Pattern, emitted: Pattern?) {
        val cell = (entry.fact.tail.ordinal * 4 + actual.fact.tail.ordinal) * 5
        admissions.incrementAndGet(cell + if (emitted == null) 4 else emitted.fact.tail.ordinal)
    }
    /** DATA row/packet attempts, not unique facts or logical paths. Bin 16 includes all larger depths. */
    fun dataRow(raw: Facts, exit: Pattern, budget: Int, route: Int) {
        restriction.incrementAndGet(0)
        restriction.incrementAndGet(7 + route)
        depth(0, maxDepth(raw))
        depth(1, exit.fact.path.count { it.isCounted() })
        depth(2, budget)
    }
    fun rejectedRow() { restriction.incrementAndGet(1) }
    fun selected(value: Facts, budget: Int) {
        restriction.incrementAndGet(2)
        restriction.incrementAndGet(3)
        val max = maxDepth(value)
        if (max > budget) restriction.incrementAndGet(5)
        depth(3, max)
    }
    fun limited(selected: Facts, value: Facts) {
        restriction.incrementAndGet(4)
        if (selected.layer == Layer.NORMAL && value.layer == Layer.DEMAND) restriction.incrementAndGet(6)
        depth(4, maxDepth(value))
    }
    /** A sampled row holds copied scalar text only. It is not propagation state. */
    fun sampleRow(method: MethodKey, member: InitialAp, raw: Facts, pair: DemandPattern,
                  budget: Int, route: Int): String? =
        samplePreparedRow(method, member.toPattern(), raw, pair, budget, route)
    fun samplePreparedRow(method: MethodKey, member: Pattern, raw: Facts, pair: DemandPattern,
                          budget: Int, route: Int): String? {
        val ordinal = sampleOrdinal.incrementAndGet()
        if (ordinal > 16 && ordinal % 4096L != 0L) return null
        return "method=${method.toString().take(300)} route=$route matchingMember=${describe(member)} " +
            "Dc=${describe(pair.entry)} Dp=${pair.exit?.let(::describe)} budget=$budget raw=${describe(raw)}"
    }
    fun sampleResult(row: String?, selected: Facts?, admitted: Facts?) {
        if (row == null) return
        val value = "$row selected=${selected?.let(::describe)} admitted=${admitted?.let(::describe)}"
        synchronized(rowSamples) {
            if (rowSamples.size == 64) rowSamples.removeFirst()
            rowSamples.addLast(value)
        }
    }
    fun rowSamples(): List<String> = synchronized(rowSamples) { rowSamples.toList() }
    private fun describe(pattern: Pattern): String {
        val mark = when (val slot = pattern.fact.mark) {
            is MarkSlot.Concrete -> slot.mark.id.toString()
            is MarkSlot.Star -> "FLOW/mx${slot.excluded.data.take(8)}"
        }
        val exclusion = (pattern.exclusion as? ExclusionSet.Concrete)?.data?.take(8) ?: emptyList()
        return "${pattern.fact.base}:${pattern.fact.path.take(12)}/${pattern.fact.tail}/$mark/E$exclusion"
    }
    private fun describe(value: Facts): String {
        val root = when (value) { is Reach -> null; is FlowTree -> value.root; is TaintTree -> value.root }
        val tail = when (value) { is Reach -> "ZERO"; is FlowTree -> value.tail.name; is TaintTree -> value.anyTail.name }
        var node = root
        val path = ArrayList<Int>()
        while (node != null && path.size < 12 && node.accessorData != null) {
            path += node.accessorData[0]; node = node.childData!![0]
        }
        val leaf = node?.leaf
        val marks = if (leaf is TaintLeaves) leaf.exact.data.take(2) + leaf.any.data.take(2) else emptyList()
        val exclusion = when (value) {
            is Reach -> ExclusionSet.Empty
            is FlowTree -> value.exclusion
            is TaintTree -> value.exclusion
        }
        val fields = (exclusion as? ExclusionSet.Concrete)?.data?.take(8) ?: emptyList()
        val mx = (value as? FlowTree)?.markExclusion?.data?.take(8) ?: emptyList()
        return "${value.base}:firstBranch$path/$tail/${value.layer}/marks$marks/maxFL${maxDepth(value)}/" +
            "protected${value is TaintTree && value.nonSubsumable != null}/E$fields/mx$mx"
    }
    private fun maxDepth(value: Facts): Int = when (value) {
        is FlowTree -> value.root.boundedDepth
        is TaintTree -> value.root.boundedDepth
        is Reach -> 0
    }
    private fun depth(kind: Int, value: Int) { depths.incrementAndGet(kind * 17 + minOf(value, 16)) }
    override fun toString(): String = listOf("c2Direct", "c2Local", "c2Visible", "c2Covered", "c2Roots",
        "c2States", "c2Joins", "c5Candidates", "c5States", "c5Restrict", "c5Covered", "c5Visible",
        "c5FixedReject", "c5Duplicate", "c5Popped", "c5Expand", "c5ComposeAttempts", "c5ComposeAccepted")
        .mapIndexed { i, name -> "$name=${values[i]}" }.joinToString(" ") + buildString {
            for ((i, name) in listOf("c5PreparedPlans", "c5PlanOccurrences", "c5AcceptedOccurrences", "c5OutputPrograms",
                "c5ProgramQueries", "c5PacketStreams", "c5ScalarEnumerations", "c5ProgramCandidates",
                "c5SelectedReferences", "c5SelectedReferencePeak", "c5BucketFallbacks", "c5StreamPacks").withIndex())
                append(" $name=${prepared[i]}")
            for ((i, name) in listOf("trieNodes", "trieProfiles", "trieCandidates").withIndex())
                append(" $name=${tries[i]}")
            for ((i, name) in listOf("Run", "StaticCompletion", "SharedCarry", "EmptyTemplates",
                "OversizeTemplates", "ZeroTemplate", "OccurrenceBudget").withIndex())
                append(" c5PlanFallback$name=${preparedFallbacks[i]}")
            for (d in Tail.entries) for (a in Tail.entries) for (result in 0..4) {
                val count = admissions[(d.ordinal * 4 + a.ordinal) * 5 + result]
                if (count != 0L) append(" c2_${d}_${a}_${if (result == 4) "REJECT" else Tail.entries[result]}=$count")
            }
            for ((i, name) in listOf("c5RowAttempts", "c5ExactRejectRows", "c5SelectedPackets", "c5LimitCalls",
                "c5LimitResults", "c5CutInputs", "c5NormalToDemandPackets", "c5LocalRows", "c5VirtualRows",
                "c5ControlRows", "c5CarryRows").withIndex()) append(" $name=${restriction[i]}")
            for ((kind, name) in listOf("Raw", "Dp", "Budget", "Selected", "Admitted").withIndex())
                for (bin in 0..16) {
                    val count = depths[kind * 17 + bin]
                    if (count != 0L) append(" c5MaxDepth${name}_${if (bin == 16) "16plus" else bin}=$count")
                }
        }
}

/** Exact query union retains both protection memberships. */
internal class ExactDemandResults(private val ap: ApManager) {
    private val values = LinkedHashSet<Facts>()
    val hasResults: Boolean get() = values.isNotEmpty()
    fun add(value: Facts) {
        ap.cancellation.checkpoint()
        values.addAll(value.membershipPackets(ap))
    }
    fun all(): List<Facts> = values.toList()
}

/** A pure local capability. Unsupported views reject before any scan or interning. */
internal interface LocalAdmissionView {
    fun supportsScan(actual: Facts, policy: RestrictedInitialPolicy): Boolean
    fun visitInitialEmissions(actual: Facts, policy: RestrictedInitialPolicy,
                              visit: (InitialEmission) -> DemandVisit): DemandScan
}

/** One ordered complete-family emitter serves native materialization and pure probes. */
internal class InitialEmissionResults(private val policy: RestrictedInitialPolicy,
                                      private val actualLayer: Layer,
                                      private val statistics: DemandQueryStatistics? = null) {
    val keys = LinkedHashSet<InitialEmission>()
    private val offered = HashSet<Pair<Pattern, Pattern>>()
    fun offer(entry: Pattern, actual: Pattern, visit: (InitialEmission) -> DemandVisit): DemandVisit {
        if (!offered.add(entry to actual)) return DemandVisit.CONTINUE
        val emissions = policy.emitAdmissions(entry, actual, actualLayer)
        statistics?.admission(entry, actual, emissions.firstOrNull()?.pattern)
        for (emitted in emissions) if (keys.add(emitted) && visit(emitted) == DemandVisit.STOP)
            return DemandVisit.STOP
        return DemandVisit.CONTINUE
    }
}

/** Compare structural keys from the scalar emitter. This check never interns hypothetical APs. */
internal class InitialDemandResults(private val ap: ApManager, private val policy: RestrictedInitialPolicy,
                                    private val actualLayer: Layer,
                                    statistics: DemandQueryStatistics? = null) {
    val initials = LinkedHashSet<AdmittedInitial>()
    private val emissions = InitialEmissionResults(policy, actualLayer, statistics)
    private val missing = HashSet<InitialEmission>()
    val fullyCovered: Boolean get() = missing.isEmpty()

    fun offer(entry: Pattern, actual: Pattern) {
        ap.cancellation.checkpoint()
        emissions.offer(entry, actual) { emitted ->
            initials += AdmittedInitial(ap.initial(emitted.pattern), emitted.layer)
            missing.remove(emitted)
            DemandVisit.CONTINUE
        }
    }
    fun has(entry: Pattern, actual: Pattern): Boolean {
        ap.cancellation.checkpoint()
        return policy.emitAdmissions(entry, actual, actualLayer).all { it in emissions.keys }
    }
    fun requireFamily(target: Pattern, flow: Boolean, actual: Pattern) {
        fun require(entry: Pattern) {
            for (potential in policy.emitAdmissions(entry, actual, actualLayer))
                if (potential !in emissions.keys) missing += potential
        }
        require(target)
        if (flow && actual.fact.mark is MarkSlot.Concrete && actual.fact.mark.mark != TaintMark.ZERO)
            require(target.copy(fact = target.fact.copy(mark = actual.fact.mark)))
    }
}
