package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.OwnedScope
import java.util.Collections

/** A run reads a fixed view. Only a complete driver barrier builds its successor. */
interface NormalTargetView {
    fun contains(method: MethodKey, premise: PremiseKey, id: ReportId): Boolean
    fun candidates(method: MethodKey, part: Subscription, mode: ApMode): List<Pair<TargetSummary, Int>>
    fun contains(method: MethodKey, scope: BlockScope?, premise: PremiseKey, id: ReportId): Boolean =
        scope == null && contains(method, premise, id)
    fun candidates(method: MethodKey, scope: BlockScope?, original: PremiseKey, actual: Facts,
                   mode: ApMode): List<Pair<TargetSummary, Int>> = emptyList()
    /** Complete snapshot, including internal scopes for future local replay. */
    fun rows(): Sequence<OwnedNormalTarget>
    /** Only public method ZERO rows participate in root report accounting. */
    fun zeroRows(): Sequence<OwnedNormalTarget> = rows().filter { it.scope == null && it.premise.isZero }

    companion object {
        val EMPTY = object : NormalTargetView {
            override fun contains(method: MethodKey, premise: PremiseKey, id: ReportId) = false
            override fun candidates(method: MethodKey, part: Subscription, mode: ApMode) = emptyList<Pair<TargetSummary, Int>>()
            override fun rows() = emptySequence<OwnedNormalTarget>()
        }
    }
}

/** Shares the existing premise index. Target identities do not change AP equality. */
class NormalTargetStore(ap: ApManager, records: Sequence<OwnedNormalTarget>) : NormalTargetView {
    private val members: Set<OwnedNormalTarget>
    private val byMethod: Map<MethodKey, PublicationIndex>
    private val byScope: Map<OwnedScope, PublicationIndex>

    init {
        val owned = LinkedHashSet<OwnedNormalTarget>()
        val indexes = LinkedHashMap<MethodKey, PublicationIndex>()
        val scoped = LinkedHashMap<OwnedScope, PublicationIndex>()
        for (record in records) {
            ap.cancellation.checkpoint()
            if (!RuntimeDataDomain.premise(record.premise) || !owned.add(record)) continue
            val index = if (record.scope == null) indexes.getOrPut(record.method) { PublicationIndex(ap, ApOps(ap)) }
                else scoped.getOrPut(OwnedScope(record.method, record.scope)) { PublicationIndex(ap, ApOps(ap)) }
            index.addTargets(listOf(TargetSummary(record.premise, Target.NormalTarget(record.id))))
        }
        members = Collections.unmodifiableSet(owned)
        byMethod = Collections.unmodifiableMap(indexes)
        byScope = Collections.unmodifiableMap(scoped)
    }

    override fun contains(method: MethodKey, premise: PremiseKey, id: ReportId): Boolean =
        OwnedNormalTarget(method, premise, id) in members
    override fun candidates(method: MethodKey, part: Subscription, mode: ApMode): List<Pair<TargetSummary, Int>> =
        byMethod[method]?.targetCandidates(part, mode).orEmpty()
    override fun contains(method: MethodKey, scope: BlockScope?, premise: PremiseKey, id: ReportId): Boolean =
        OwnedNormalTarget(method, premise, id, scope) in members
    override fun candidates(method: MethodKey, scope: BlockScope?, original: PremiseKey, actual: Facts,
                            mode: ApMode): List<Pair<TargetSummary, Int>> =
        (if (scope == null) byMethod[method] else byScope[OwnedScope(method, scope)])
            ?.targetCandidates(original, actual, mode).orEmpty()
    override fun rows(): Sequence<OwnedNormalTarget> = members.asSequence()
}
