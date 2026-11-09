package org.opentaint.dataflow.bidi.ap

/** Query-local selections. Each stream keeps its own native exclusion/tail header. */
internal class ProgramBucket {
    val protectedSelections = LinkedHashSet<Conclusion>()
    val ordinarySelections = LinkedHashSet<Conclusion>()
}

/** Optional diagnostics; no stream or AP value is retained by a counter. */
internal interface DemandScalarWork {
    fun stream() = Unit
    fun scalar() = Unit
    fun candidate() = Unit
    fun selectedReference(size: Int) = Unit
    fun overflow() = Unit
    fun pack() = Unit
}

/** The same protected-first traversal as transportProtection, with independent headers. */
internal fun forEachDemandScalar(ops: ApOps, raw: Facts, work: DemandScalarWork?,
                                visit: (protected: Boolean, scalar: Conclusion) -> Boolean) {
    fun stream(value: Facts, protected: Boolean): Boolean {
        work?.stream()
        for (leaf in ops.leaves(value)) {
            ops.manager.cancellation.checkpoint()
            work?.scalar()
            if (!visit(protected, Conclusion(leaf.fact, leaf.exclusion, value.layer == Layer.DEMAND))) return false
        }
        return true
    }
    for (packet in raw.membershipPackets(ops.manager)) {
        val protected = packet is TaintTree && packet.protectionClass()
        if (!stream(packet.withoutProtection(), protected)) return
    }
}

/** Preserve native whole-program packing, protected masks and first header order. */
internal fun packProgramStreams(ops: ApOps, bucket: ProgramBucket, work: DemandScalarWork? = null): List<Facts> {
    val result = ArrayList<Facts>()
    if (bucket.ordinarySelections.isNotEmpty()) {
        work?.pack()
        result += packRestrictedSelections(ops, bucket.ordinarySelections)
    }
    if (bucket.protectedSelections.isNotEmpty()) {
        work?.pack()
        for (value in packRestrictedSelections(ops, bucket.protectedSelections))
            result += if (value is TaintTree) value.withProtection(value.root) else value
    }
    return result
}
