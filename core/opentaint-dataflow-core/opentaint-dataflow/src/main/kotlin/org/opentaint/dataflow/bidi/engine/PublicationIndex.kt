package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.PathTrie
import org.opentaint.dataflow.bidi.store.FlowBackedSummaries
import java.util.Collections

/** Candidate lookup preserves the full premise and the member that matched its position. */
class PublicationIndex(private val ap: ApManager, private val ops: ApOps, flowBacked: Boolean = false) {
    private data class Member(val premise: PremiseKey, val index: Int)
    private val interners = ap.newInterners()
    private val merged = LinkedHashMap<PremiseKey, ConclusionGroup>()
    private val backed = if (flowBacked) FlowBackedSummaries(ap) else null
    private val targets = LinkedHashMap<PremiseKey, LinkedHashSet<Target>>()
    private val indexed = java.util.Collections.newSetFromMap(java.util.IdentityHashMap<PremiseKey, Boolean>())
    private val byMember = PathTrie<Member>(ap.cancellation)
    fun addAll(pubs: List<Publication>): List<Publication> {
        ap.cancellation.checkpoint()
        val out = ArrayList<Publication>()
        for (pub in pubs) {
            ap.cancellation.checkpoint()
            if (!RuntimeDataDomain.packet(pub.premise, pub.conclusion)) continue
            assertCanonicalFlowSummary(pub.premise, pub.conclusion)
            check(pub.conclusion.base !is AccessPathBase.CleanerTemporary) {
                "A field-action temporary cannot enter a publication"
            }
            check((pub.conclusion is FlowTree) == pub.premise.isFlow) {
                "K6: the conclusion kind follows its premise"
            }
            check(pub.premise !is PremiseSet || pub.conclusion is TaintTree) {
                "A multi-premise publication must be TAINT"
            }
            val fresh = if (backed != null) backed.add(pub.premise, pub.conclusion)
                else merged.getOrPut(pub.premise) { ConclusionGroup(ap, interners) }.add(pub.conclusion)
            if (fresh == null) continue
            indexPremise(pub.premise)
            out += Publication(pub.premise, fresh)
        }
        // FLOW can arrive after a marked delta in this same detached batch.
        // Normalize before notifying callers, as well as before later replay.
        val current = if (backed == null) out else out.mapNotNull { pub ->
            backed.normalize(pub.premise, pub.conclusion)?.let { Publication(pub.premise, it) }
        }
        return Collections.unmodifiableList(current)
    }

    private fun indexPremise(premise: PremiseKey) {
        if (!indexed.add(premise)) return
        for (member in 0 until premise.size) {
            ap.cancellation.checkpoint()
            val initial = premise.member(member)
            byMember.add(initial.base, initial.pathData, Member(premise, member))
        }
    }

    fun addTargets(rows: TargetBatch): TargetBatch {
        val fresh = ArrayList<TargetSummary>()
        for (row in rows) {
            ap.cancellation.checkpoint()
            if (!RuntimeDataDomain.premise(row.premise)) continue
            if (!targets.getOrPut(row.premise, ::LinkedHashSet).add(row.target)) continue
            indexPremise(row.premise)
            fresh += row
        }
        return Collections.unmodifiableList(fresh)
    }

    private fun candidateMembers(original: PremiseKey, actual: Facts, mode: ApMode, zeroOnly: Boolean): Set<Member> {
        ap.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(original, actual)) return emptySet()
        val members = LinkedHashSet<Member>()
        if (zeroOnly) {
            for (member in byMember.lookupExtensions(AccessPathBase.Zero, EMPTY_PATH)) {
                ap.cancellation.checkpoint()
                if (member.premise.isZero) members += member
            }
        } else {
            for (leaf in ops.leaves(actual)) {
                ap.cancellation.checkpoint()
                val path = leaf.fact.path.toIntArray()
                if (mode.run1) {
                    members += byMember.lookupPrefixes(leaf.fact.base, path)
                    if (leaf.fact.tail != Tail.EXACT) {
                        // A nonexact actual ancestor can supply a requested
                        // component. The complete AP predicate checks its E,
                        // marks and tail after this candidate lookup.
                        members += byMember.lookupExtensions(leaf.fact.base, path)
                    }
                }
                else {
                    members += byMember.lookupExtensions(leaf.fact.base, path)
                    for (member in byMember.lookupPrefixes(leaf.fact.base, path)) {
                        ap.cancellation.checkpoint()
                        if (member.premise.member(member.index).let { it.mark is MarkSlot.Star || it.tail == Tail.STAR }) members += member
                    }
                }
            }
        }
        return members
    }

    fun candidates(part: Subscription, mode: ApMode): List<Pair<Publication, Int>> =
        candidates(part.ref.premise, part.added, mode, part.zeroOnly)

    fun candidates(original: PremiseKey, actual: Facts, mode: ApMode,
                   zeroOnly: Boolean = false): List<Pair<Publication, Int>> {
        val out = ArrayList<Pair<Publication, Int>>()
        for (member in candidateMembers(original, actual, mode, zeroOnly)) {
            ap.cancellation.checkpoint()
            for (publication in publications(member.premise)) out += publication to member.index
        }
        return Collections.unmodifiableList(out)
    }

    fun targetCandidates(part: Subscription, mode: ApMode): List<Pair<TargetSummary, Int>> =
        targetCandidates(part.ref.premise, part.added, mode, part.zeroOnly)

    fun targetCandidates(original: PremiseKey, actual: Facts, mode: ApMode,
                         zeroOnly: Boolean = false): List<Pair<TargetSummary, Int>> {
        val out = ArrayList<Pair<TargetSummary, Int>>()
        for (member in candidateMembers(original, actual, mode, zeroOnly)) {
            ap.cancellation.checkpoint()
            for (target in targets[member.premise].orEmpty()) out += TargetSummary(member.premise, target) to member.index
        }
        return Collections.unmodifiableList(out)
    }

    fun staticTargetCandidates(): List<Pair<TargetSummary, Int>> {
        val out = ArrayList<Pair<TargetSummary, Int>>()
        for (member in byMember.lookupExtensions(STATIC, EMPTY_PATH)) {
            ap.cancellation.checkpoint()
            for (target in targets[member.premise].orEmpty()) out += TargetSummary(member.premise, target) to member.index
        }
        return Collections.unmodifiableList(out)
    }

    /** Borrow the existing publication rows. No duplicate static-summary store. */
    fun staticCandidates(): List<Pair<Publication, Int>> {
        ap.cancellation.checkpoint()
        val out = ArrayList<Pair<Publication, Int>>()
        for (member in byMember.lookupExtensions(STATIC, EMPTY_PATH)) {
            ap.cancellation.checkpoint()
            for (publication in publications(member.premise)) {
                ap.cancellation.checkpoint()
                out += publication to member.index
            }
        }
        return Collections.unmodifiableList(out)
    }

    private fun publications(premise: PremiseKey): List<Publication> {
        val values = backed?.borrow(premise) ?: merged[premise]?.all() ?: emptySequence()
        return values.map { Publication(premise, it) }.toList()
    }
}
