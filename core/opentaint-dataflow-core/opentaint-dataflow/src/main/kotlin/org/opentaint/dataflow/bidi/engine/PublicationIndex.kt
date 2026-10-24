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
    private val indexed = java.util.Collections.newSetFromMap(java.util.IdentityHashMap<PremiseKey, Boolean>())
    private val byMember = PathTrie<Member>(ap.cancellation)
    fun addAll(pubs: List<Publication>): List<Publication> {
        ap.cancellation.checkpoint()
        val out = ArrayList<Publication>()
        for (pub in pubs) {
            ap.cancellation.checkpoint()
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
            if (indexed.add(pub.premise)) {
                for (member in 0 until pub.premise.size) {
                    ap.cancellation.checkpoint()
                    val initial = pub.premise.member(member)
                    byMember.add(initial.base, initial.pathData, Member(pub.premise, member))
                }
            }
            out += Publication(pub.premise, fresh)
        }
        // FLOW can arrive after a marked delta in this same detached batch.
        // Normalize before notifying callers, as well as before later replay.
        val current = if (backed == null) out else out.mapNotNull { pub ->
            backed.normalize(pub.premise, pub.conclusion)?.let { Publication(pub.premise, it) }
        }
        return Collections.unmodifiableList(current)
    }

    fun candidates(part: Subscription, mode: ApMode): List<Pair<Publication, Int>> {
        ap.cancellation.checkpoint()
        val members = LinkedHashSet<Member>()
        if (part.zeroOnly) {
            for (member in byMember.lookupExtensions(AccessPathBase.Zero, EMPTY_PATH)) {
                ap.cancellation.checkpoint()
                if (member.premise.isZero) members += member
            }
        } else {
            for (leaf in ops.leaves(part.added)) {
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
                        if (member.premise.member(member.index).mark is MarkSlot.Star) members += member
                    }
                }
            }
        }
        val out = ArrayList<Pair<Publication, Int>>()
        for (member in members) {
            ap.cancellation.checkpoint()
            for (publication in publications(member.premise)) {
                ap.cancellation.checkpoint()
                out += publication to member.index
            }
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
