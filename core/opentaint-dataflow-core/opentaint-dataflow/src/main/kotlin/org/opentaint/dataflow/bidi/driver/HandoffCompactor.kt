package org.opentaint.dataflow.bidi.driver

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.TargetSummary
import org.opentaint.dataflow.bidi.store.*

/** One whole original, not one ND arm. All projected leaves/members belong to it. */
internal class HandoffOrigin(
    val owner: HandoffOwner,
    val protected: Boolean,
    val rows: List<PairedDemand>,
    val orderKey: String,
)
internal data class HandoffWitness(val provider: HandoffOrigin, val row: PairedDemand)
internal class HandoffSelection(
    val kept: List<HandoffOrigin>,
    val certificates: Map<HandoffOrigin, List<HandoffWitness>>,
)

/** Exact C2/C5 service compaction. R3 request-language/MAY-only removals are not
 * enabled: their native eventual-refinement proof is still open. */
internal class HandoffCompactor(private val ap: ApManager) {
    private val keys = HandoffServiceKeys(ap)

    fun summary(owner: HandoffOwner, premise: PremiseKey, facts: Facts): HandoffOrigin {
        val rows = projectSummaryGuidance(ap, premise, facts)
        return HandoffOrigin(owner, facts is TaintTree && facts.protectionClass(), rows,
            "S:${facts.layer}:${premise.size}:" +
                premise.members.map { keys.order(it.toPattern()) }.sorted().joinToString("") + "->" +
                ApOps(ap).leaves(facts).map(keys::order).sorted().joinToString(""))
    }

    fun target(owner: HandoffOwner, row: TargetSummary): HandoffOrigin {
        val rows = projectTargetGuidance(row)
        return HandoffOrigin(owner, false, rows, "T:" +
            row.premise.members.map { keys.order(it.toPattern()) }.sorted().joinToString(""))
    }

    fun select(origins: List<HandoffOrigin>): HandoffSelection {
        // Different method/context/block entries cannot cover each other. Grouping
        // avoids one global sort or comparisons of opaque context allocation IDs.
        val kept = ArrayList<HandoffOrigin>(origins.size)
        val certificates = LinkedHashMap<HandoffOrigin, List<HandoffWitness>>()
        for (group in origins.groupBy { it.owner.entryOwner }.values) {
            ap.cancellation.checkpoint()
            selectGroup(group, kept, certificates)
        }
        return HandoffSelection(kept, certificates)
    }

    private fun selectGroup(origins: List<HandoffOrigin>, result: MutableList<HandoffOrigin>,
                            certificates: MutableMap<HandoffOrigin, List<HandoffWitness>>) {
        val sorted = origins.sortedWith(compareBy<HandoffOrigin>({ it.owner.exit?.ordinal ?: -1 },
            { it.protected }, { it.orderKey }))
        val active = LinkedHashSet(sorted)
        val c2 = HashMap<HandoffC2Key, LinkedHashMap<HandoffOrigin, PairedDemand>>()
        val c5 = HashMap<HandoffC5Key, LinkedHashMap<HandoffOrigin, PairedDemand>>()
        for (origin in sorted) for (row in origin.rows) {
            c2.getOrPut(keys.c2(origin,row),::LinkedHashMap).putIfAbsent(origin,row)
            c5.getOrPut(keys.c5(origin,row),::LinkedHashMap).putIfAbsent(origin,row)
        }
        val dependents = HashMap<HandoffOrigin, MutableSet<HandoffOrigin>>()
        fun proof(origin: HandoffOrigin, excluded: HandoffOrigin): List<HandoffWitness>? {
            if (origin.rows.isEmpty()) return null
            val witnesses = ArrayList<HandoffWitness>(origin.rows.size * 2)
            for (row in origin.rows) {
                ap.cancellation.checkpoint()
                val entry = c2[keys.c2(origin,row)]?.entries?.firstOrNull { it.key !== excluded }
                    ?: return null
                witnesses += HandoffWitness(entry.key, entry.value)
                var output: HandoffWitness? = null
                for (key in keys.c5Alternatives(keys.c5(origin,row))) {
                    val found = c5[key]?.entries?.firstOrNull { it.key !== excluded } ?: continue
                    output = HandoffWitness(found.key, found.value)
                    break
                }
                witnesses += output ?: return null
            }
            return witnesses
        }
        for (origin in sorted) {
            ap.cancellation.checkpoint()
            val affected = dependents[origin].orEmpty().toList()
            val replacements = LinkedHashMap<HandoffOrigin, List<HandoffWitness>>()
            var valid = true
            for (old in affected + origin) {
                val next = proof(old,origin)
                if (next == null) { valid = false; break }
                replacements[old] = next
            }
            if (!valid) continue
            active.remove(origin)
            for (row in origin.rows) {
                c2[keys.c2(origin,row)]?.remove(origin)
                c5[keys.c5(origin,row)]?.remove(origin)
            }
            for ((old, witnesses) in replacements) {
                certificates[old]?.forEach { dependents[it.provider]?.remove(old) }
                certificates[old] = witnesses
                witnesses.forEach { dependents.getOrPut(it.provider,::LinkedHashSet).add(old) }
            }
            dependents.remove(origin)
        }
        for (origin in origins) check(certificates[origin].orEmpty().all { it.provider in active })
        result += active
    }
}

/** The single native projection used by ordinary and compacted method/block handoff. */
internal fun projectSummaryGuidance(ap: ApManager, premise: PremiseKey, facts: Facts): List<PairedDemand> {
    val result = ArrayList<PairedDemand>()
    for (leaf in ApOps(ap).leaves(facts)) {
        ap.cancellation.checkpoint()
        val entry = guidancePattern(leaf)
        premise.forEachMember { member ->
            ap.cancellation.checkpoint()
            val from = guidancePattern(member.toPattern())
            result += PairedDemand(
                if (entry.fact.base == AccessPathBase.Zero) DemandEntry.Zero else DemandEntry.Data(entry),
                if (from.fact.base == AccessPathBase.Zero) DemandExit.Zero else DemandExit.Data(from))
        }
    }
    return result
}

internal fun projectTargetGuidance(row: TargetSummary): List<PairedDemand> {
    check(row.target == org.opentaint.dataflow.bidi.engine.Target.DemandTarget)
    return row.premise.members.map { member -> PairedDemand(DemandEntry.Target,
        if (member.isZero) DemandExit.Zero else DemandExit.Data(guidancePattern(member.toPattern()))) }
}
