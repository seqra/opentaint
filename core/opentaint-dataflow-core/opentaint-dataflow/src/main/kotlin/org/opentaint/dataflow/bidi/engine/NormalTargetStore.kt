package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import java.util.Collections

/** A run reads a fixed view. Only a complete driver barrier builds its successor. */
interface NormalTargetView {
    fun contains(method: MethodKey, premise: PremiseKey, id: ReportId): Boolean
    fun candidates(method: MethodKey, part: Subscription, mode: ApMode): List<Pair<TargetSummary, Int>>
    fun rows(): Sequence<OwnedNormalTarget>
    fun zeroRows(): Sequence<OwnedNormalTarget> = rows().filter { it.premise.isZero }

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

    init {
        val owned = LinkedHashSet<OwnedNormalTarget>()
        val indexes = LinkedHashMap<MethodKey, PublicationIndex>()
        for (record in records) {
            ap.cancellation.checkpoint()
            if (!RuntimeDataDomain.premise(record.premise) || !owned.add(record)) continue
            indexes.getOrPut(record.method) { PublicationIndex(ap, ApOps(ap)) }
                .addTargets(listOf(TargetSummary(record.premise, Target.NormalTarget(record.id))))
        }
        members = Collections.unmodifiableSet(owned)
        byMethod = Collections.unmodifiableMap(indexes)
    }

    override fun contains(method: MethodKey, premise: PremiseKey, id: ReportId): Boolean =
        OwnedNormalTarget(method, premise, id) in members
    override fun candidates(method: MethodKey, part: Subscription, mode: ApMode): List<Pair<TargetSummary, Int>> =
        byMethod[method]?.targetCandidates(part, mode).orEmpty()
    override fun rows(): Sequence<OwnedNormalTarget> = members.asSequence()
}
