package org.opentaint.dataflow.bidi.store

import kotlinx.collections.immutable.PersistentMap
import kotlinx.collections.immutable.persistentHashMapOf
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.Collections

/** Rule identity only. No compiled predicate, transfer, or callback is retained. */
sealed interface NormalRuleDescriptor {
    data class Predicate(val occurrence: RuleOccurrenceId) : NormalRuleDescriptor

    class LegacyConjunction internal constructor(literals: List<Pattern>, target: PathFact) : NormalRuleDescriptor {
        private val literals = snapshotPatterns(literals)
        private val target = snapshotFact(target)
        private val hash = 31 * this.literals.hashCode() + this.target.hashCode()
        override fun hashCode(): Int = hash
        override fun equals(other: Any?): Boolean = this === other || other is LegacyConjunction &&
            literals == other.literals && target == other.target
    }

    class LegacySink internal constructor(private val configuration: CommonTaintConfigurationSink,
                                         private val alternative: Int, patterns: List<Pattern>) : NormalRuleDescriptor {
        private val patterns = snapshotPatterns(patterns)
        private val hash = 31 * (31 * configuration.hashCode() + alternative) + this.patterns.hashCode()
        override fun hashCode(): Int = hash
        override fun equals(other: Any?): Boolean = this === other || other is LegacySink &&
            configuration == other.configuration && alternative == other.alternative && patterns == other.patterns
    }

    companion object {
        fun predicate(occurrence: RuleOccurrenceId): NormalRuleDescriptor = Predicate(occurrence)
        fun legacyConjunction(edge: ConjunctiveEdge): NormalRuleDescriptor = LegacyConjunction(edge.literals, edge.target)
        fun legacySink(sink: SinkRule): NormalRuleDescriptor = LegacySink(sink.rule, sink.alternative, sink.patterns)
    }
}

private fun snapshotFact(fact: PathFact): PathFact =
    fact.copy(path = Collections.unmodifiableList(fact.path.toList()))
private fun snapshotPatterns(patterns: List<Pattern>): List<Pattern> =
    Collections.unmodifiableList(patterns.map { it.copy(fact = snapshotFact(it.fact)) })

/** These values describe a condition point, never a request/resume address. */
sealed interface NormalRulePhase {
    data object Statement : NormalRulePhase
    data class Boundary(val atStart: Boolean) : NormalRulePhase
    data object CallStage : NormalRulePhase
    data object CallSinkBound : NormalRulePhase
    data class Cleaner(val step: Int, val phase: CleanerPhase) : NormalRulePhase
    data class ReadOutput(val input: NormalRuleSite) : NormalRulePhase
}

data class NormalRuleSite(
    val statement: CommonInst,
    val stageOrdinal: Int,
    val action: ActionId?,
    val substep: Int,
    val phase: NormalRulePhase,
) {
    companion object {
        /** Strip the transient operation FormOwner. A sink observes semantic BOUND,
         * independent of which outgoing BOUND stage supplied a resume address. */
        fun of(rule: NormalRuleDescriptor, site: ResumeSite): NormalRuleSite {
            val sink = rule is NormalRuleDescriptor.LegacySink ||
                rule is NormalRuleDescriptor.Predicate && rule.occurrence.kind == RuleKind.CALL_SINK
            val operation = site.operation
            val phase = when (site) {
                is ResumeSite.StatementInput -> NormalRulePhase.Statement
                is ResumeSite.BoundaryInput -> NormalRulePhase.Boundary(site.atStart)
                is ResumeSite.CallStageInput -> if (sink) NormalRulePhase.CallSinkBound else NormalRulePhase.CallStage
                is ResumeSite.CleanerInput -> NormalRulePhase.Cleaner(site.step, site.phase)
                is ResumeSite.ReadOutput -> NormalRulePhase.ReadOutput(of(rule, site.input))
            }
            return NormalRuleSite(operation.form.statement,
                if (phase == NormalRulePhase.CallSinkBound) 0 else operation.stageOrdinal,
                operation.action, operation.substep, phase)
        }
    }
}

data class NormalRuleContributorOwner(val method: MethodKey, val scope: BlockScope, val markMode: MarkMode,
                                      val direction: Direction = Direction.FORWARD)
data class NormalRuleContributorKey(val owner: NormalRuleContributorOwner, val rule: NormalRuleDescriptor,
                                    val site: NormalRuleSite)
data class NormalRuleContributorRow(val key: NormalRuleContributorKey, val leaf: Int,
                                    val input: ConjunctionStore.Input) {
    init { require(leaf >= 0) }
}

/** Immutable previous-run input. It offers no write or executable transfer API. */
interface NormalRuleContributorView {
    val retainedRows: Long
    fun rows(key: NormalRuleContributorKey): List<NormalRuleContributorRow>
    fun allRows(): List<NormalRuleContributorRow>

    companion object {
        val EMPTY: NormalRuleContributorView = object : NormalRuleContributorView {
            override val retainedRows = 0L
            override fun rows(key: NormalRuleContributorKey) = emptyList<NormalRuleContributorRow>()
            override fun allRows() = emptyList<NormalRuleContributorRow>()
        }
    }
}

private data class NormalInputHeader(val leaf: Int, val premise: PremiseKey, val group: GroupKey)
private data class NormalContributorRoot(
    val entries: PersistentMap<NormalRuleContributorKey, PersistentMap<NormalInputHeader, NormalRuleContributorRow>> = persistentHashMapOf(),
    val size: Long = 0,
)

/** One barrier writer publishes a complete persistent-map root. Existing views
 * remain immutable even when a later publication fails or is cancelled. */
class NormalRuleContributorStore(private val manager: ApManager) {
    @Volatile private var published = NormalContributorRoot()
    val retainedRows: Long get() = published.size

    fun snapshot(): NormalRuleContributorView = Snapshot(published)

    /** Returns true for new geometry or metadata. DEMAND and unsupported modes
     * are excluded; no partially built root is visible to a reader. */
    fun publish(rows: Iterable<NormalRuleContributorRow>): Boolean {
        val previous = published
        var next = previous
        for (row in rows) {
            manager.cancellation.checkpoint()
            val input = row.input
            val facts = input.facts ?: continue
            if (row.key.owner.direction != Direction.FORWARD || row.key.owner.markMode != MarkMode.FULL ||
                input.layer != Layer.NORMAL || facts.layer != Layer.NORMAL ||
                !RuntimeDataDomain.packet(input.premise, facts)) continue
            check((facts is FlowTree) == input.premise.isFlow) { "A saved condition keeps the original conclusion kind" }
            check(input.premise !is PremiseSet || facts is TaintTree)
            val header = NormalInputHeader(row.leaf, input.premise, facts.groupKey)
            val members = next.entries[row.key] ?: persistentHashMapOf()
            val old = members[header]
            val retained = if (old == null) row else {
                val (merged, delta) = manager.mergeAddDelta(checkNotNull(old.input.facts), facts)
                if (delta == null) continue
                old.copy(input = old.input.copy(facts = merged))
            }
            next = NormalContributorRoot(next.entries.put(row.key, members.put(header, retained)),
                next.size + if (old == null) 1 else 0)
        }
        manager.cancellation.checkpoint()
        published = next
        return next !== previous
    }

    private class Snapshot(private val root: NormalContributorRoot) : NormalRuleContributorView {
        override val retainedRows get() = root.size
        override fun rows(key: NormalRuleContributorKey): List<NormalRuleContributorRow> =
            Collections.unmodifiableList(root.entries[key]?.values?.toList().orEmpty())
        override fun allRows(): List<NormalRuleContributorRow> =
            Collections.unmodifiableList(root.entries.values.flatMap { it.values })
    }
}
