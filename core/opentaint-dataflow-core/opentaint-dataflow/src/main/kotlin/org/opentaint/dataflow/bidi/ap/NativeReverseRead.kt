package org.opentaint.dataflow.bidi.ap

/** Constructor provenance is transient and does not change stored AP or Record equality. */
enum class NativeReadKind { GENERIC, FLOW_MUST, CONCRETE_MUST }

data class NativeReadKey(val view: RecordLeafView, val mustOverlap: Boolean)

class NativeReverseRead internal constructor(
    val view: RecordLeafView,
    val kind: NativeReadKind,
    val sourceDirection: Direction,
    val sourcePremise: Pattern,
    val sourceConclusion: Conclusion,
) {
    val mayUseMustOverlap: Boolean = kind != NativeReadKind.GENERIC &&
        sourceConclusion.fact.tail == Tail.ANY_TAINT

    fun semanticKey(): NativeReadKey = NativeReadKey(view, mayUseMustOverlap)
}

/** Legacy matching first, then the newly selected same-path STAR overlap contribution.
 * Each packet retains its own header; the projection never changes the standing input. */
internal fun matchOppositeRecordPackets(ops: ApOps, actual: Facts, read: NativeReverseRead,
                                        mode: ApMode): List<Facts> {
    require(read.sourceDirection != mode.direction) { "A native inverse is read in the opposite direction" }
    val ap = ops.manager
    val result = ArrayList<Facts>(2)
    for (packet in ap.canonicalPackets(actual)) {
        ap.cancellation.checkpoint()
        ops.matchSummary(packet, read.view.premise, mode, nativeRecordRead = true,
            role = SummaryMatchRole.OPPOSITE_RECORD)?.let(result::add)
        if (!read.mayUseMustOverlap || read.view.premise.fact.tail != Tail.STAR) continue
        val query = read.view.premise
        if (packet.base != query.fact.base) continue
        val exclusion = when (packet) {
            is FlowTree -> packet.exclusion.takeIf { packet.tail == Tail.STAR }
            is TaintTree -> packet.exclusion.takeIf { packet.anyTail == Tail.STAR }
            is Reach -> null
        } ?: continue
        if (exclusion.isSubsetOf(query.exclusion) || query.exclusion.isSubsetOf(exclusion)) continue
        val path = query.fact.path.toIntArray()
        val projectedE = ap.intern(exclusion.union(query.exclusion))
        val projected = when (packet) {
            is FlowTree -> {
                val at = packet.root.walk(path) { _, _ -> ap.cancellation.checkpoint() }
                if (at == null || at.leaf.isEmpty) null else ap.flowTree(packet.base, packet.layer,
                    projectedE, packet.markExclusion,
                    FlowAlgebra.prepend(ap, ap.path(query.fact.path), FlowAlgebra.LEAF_NODE), Tail.STAR)
            }
            is TaintTree -> {
                val at = packet.root.walk(path) { _, _ -> ap.cancellation.checkpoint() }
                val marks = at?.leaf?.any
                if (marks == null || marks.isEmpty) null else retainProtection(packet,
                    ap.taintTree(packet.base, packet.layer,
                        ap.taintAlg.prepend(ap, ap.path(query.fact.path),
                            ap.taintAlg.leafNode(ap.taintLeaves(MarkSet.EMPTY, marks))), projectedE, Tail.STAR),
                    ap.cancellation)
            }
            is Reach -> null
        } ?: continue
        ops.matchSummary(projected, query, mode, nativeRecordRead = true,
            role = SummaryMatchRole.OPPOSITE_RECORD)?.let(result::add)
    }
    return result
}
