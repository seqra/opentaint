package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*

internal data class OutputProgramKey(val fullExit: Pattern, val fieldBudget: Int)

/** The representative is a capability obtained after one exact paired entry check. */
internal class OutputProgram(
    val ordinal: Int,
    val key: OutputProgramKey,
    val representative: AcceptedEntryOutput,
)

/** Immutable within one exact normalized whole-original/scope/policy query. */
internal class PreparedOutputPrograms private constructor(
    private val ap: ApManager,
    private val method: MethodKey,
    private val templates: List<Pattern>,
    private val programs: List<OutputProgram>,
    private val outputs: FrozenDemandTrie<Int>,
    override val rowChecks: Int,
    private val statistics: DemandQueryStatistics?,
) : PreparedLocalDataPlan {
    override val outputProgramCount: Int get() = programs.size
    override fun emptyForBase(base: AccessPathBase): Boolean = !outputs.hasBase(base)

    override fun intersect(original: PremiseKey, raw: Facts): List<Facts>? {
        ap.cancellation.checkpoint()
        if (raw is Reach || original.isZero || original.members.map { it.toPattern() } != templates) return null
        if (!RuntimeDataDomain.packet(original, raw)) return emptyList()
        statistics?.preparedQuery()
        if (!outputs.hasBase(raw.base)) return emptyList()
        val ops = ApOps(ap)
        val buckets = arrayOfNulls<ProgramBucket>(programs.size)
        var references = 0
        var overflow = false
        forEachDemandScalar(ops, raw, statistics) { protected, scalar ->
            if (!overflow) outputs.visitNativeOrder(Pattern(scalar.fact, scalar.exclusion),
                DemandQueryKind.OUTPUT_C5, ap.marks) { ordinal ->
                if (!overflow) {
                    ap.cancellation.checkpoint()
                    statistics?.candidate()
                    val program = programs[ordinal]
                    val selected = restrictConclusionOnly(scalar, program.representative.fullExit, ap.marks)
                    if (selected != null) {
                        val bucket = buckets[ordinal] ?: ProgramBucket().also { buckets[ordinal] = it }
                        val selections = if (protected) bucket.protectedSelections else bucket.ordinarySelections
                        if (selections.add(selected)) {
                            references++
                            statistics?.selectedReference(references)
                            if (references > MAX_SELECTED_REFERENCES) {
                                overflow = true
                                statistics?.overflow()
                            }
                        }
                    }
                }
            }
            !overflow
        }
        // No partial output escapes an oversized pure query. Native C5 recomputes it.
        if (overflow) return null
        val result = ExactDemandResults(ap)
        for (program in programs) {
            ap.cancellation.checkpoint()
            statistics?.add(7)
            statistics?.add(9)
            statistics?.dataRow(raw, program.key.fullExit, program.key.fieldBudget, route = 0)
            val sample = statistics?.samplePreparedRow(method, program.representative.initial,
                raw, program.representative.pair, program.key.fieldBudget, route = 0)
            val bucket = buckets[program.ordinal]
            if (bucket == null) {
                statistics?.rejectedRow()
                statistics?.sampleResult(sample, null, null)
                continue
            }
            for (packet in packProgramStreams(ops, bucket, statistics)) {
                statistics?.selected(packet, program.key.fieldBudget)
                ops.limit(packet, program.key.fieldBudget, object : ApOut {
                    override fun result(f: Facts) {
                        statistics?.limited(packet, f)
                        statistics?.sampleResult(sample, packet, f)
                        result.add(f)
                    }
                    override fun markRequest(mark: TaintMark) = error("A field cut must not emit a mark request")
                })
            }
        }
        return result.all()
    }

    class Builder(private val ap: ApManager, private val method: MethodKey, private val templates: List<Pattern>,
                  private val policy: RestrictedInitialPolicy,
                  private val statistics: DemandQueryStatistics?) {
        private val programs = LinkedHashMap<OutputProgramKey, OutputProgram>()
        private var checks = 0
        private var accepted = 0

        /** Call for every native member/prefix/row occurrence, including rejected rows. */
        fun offer(ticket: EntryRestrictionTicket?) {
            checks++
            if (ticket == null) return
            accepted++
            val output = ticket.acceptedOutput() ?: return
            val depth = output.fullExit.fact.path.count { it.isCounted() }
            val global = policy.fieldLimit
            check(global >= 1)
            val key = OutputProgramKey(output.fullExit, if (depth >= global) global else depth + 1)
            programs.getOrPut(key) { OutputProgram(programs.size, key, output) }
        }

        fun build(): PreparedOutputPrograms {
            val outputs = FrozenDemandTrie.Builder<Int>(ap.cancellation)
            for (program in programs.values) outputs.add(program.key.fullExit, program.ordinal)
            statistics?.preparedPlan(checks, accepted, programs.size)
            return PreparedOutputPrograms(ap, method, templates.toList(), programs.values.toList(),
                outputs.build(), checks, statistics)
        }
    }

    companion object {
        internal const val MAX_SELECTED_REFERENCES = 2048
    }
}
