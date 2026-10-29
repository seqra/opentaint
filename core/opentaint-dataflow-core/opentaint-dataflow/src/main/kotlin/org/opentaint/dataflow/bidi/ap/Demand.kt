package org.opentaint.dataflow.bidi.ap


/** The caller enforces the run's must-premise mode before starting an initial. */
internal fun initialFacts(m: ApManager, i: InitialAp): Facts {
    m.cancellation.checkpoint()
    if (i.isZero) return Reach.NORMAL
    return when (val mark = i.mark) {
        is MarkSlot.Star -> {
            val layer = when (i.tail) {
                Tail.STAR -> Layer.NORMAL
                Tail.ANY -> Layer.DEMAND
                Tail.EXACT, Tail.ANY_TAINT -> Layer.NORMAL
            }
            m.flowTree(i.base, layer, i.exclusion, MarkSet.EMPTY,
                FlowAlgebra.prepend(m, i.path, FlowAlgebra.LEAF_NODE), i.tail)
        }
        is MarkSlot.Concrete -> {
            val marks = m.markSetOf(mark.mark)
            val exact = i.tail == Tail.EXACT
            val leaf = if (exact) m.taintLeaves(marks, MarkSet.EMPTY) else m.taintLeaves(MarkSet.EMPTY, marks)
            val layer = if (exact || i.tail == Tail.ANY_TAINT) Layer.NORMAL else Layer.DEMAND
            m.taintTree(i.base, layer, m.taintAlg.prepend(m, i.path, m.taintAlg.leafNode(leaf)),
                if (i.tail == Tail.STAR || i.tail == Tail.ANY_TAINT) i.exclusion else ExclusionSet.Empty,
                anyTail = if (exact) Tail.ANY_TAINT else i.tail)
        }
    }
}

internal fun policyInitial(m: ApManager, added: Facts): InitialAp {
    m.cancellation.checkpoint()
    return if (added is Reach) m.zero
        else m.initial(added.base, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)
}

/** An abstract entry shares one FLOW initial across matching concrete marks and exit patterns. */
internal fun emitInitials(ops: ApOps, d: DemandPattern, added: Facts,
                          policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = ops.manager.marks)): List<InitialAp> {
    val m = ops.manager
    m.cancellation.checkpoint()
    check(d.entry.fact.tail != Tail.ANY_TAINT) { "W8 (d): a demand entry cannot have a must tail" }
    val result = LinkedHashSet<InitialAp>()
    for (a in ops.leaves(added)) {
        m.cancellation.checkpoint()
        val j = policy.emit(d.entry, a) ?: continue
        result += m.initial(j)
    }
    return result.toList()
}

/** Preserve the reference result, including shapes outside typed Facts. */
internal fun restrictRaw(ops: ApOps, j: InitialAp, g: Facts, d: DemandPattern,
                         policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = ops.manager.marks)): List<Conclusion> {
    val m = ops.manager
    m.cancellation.checkpoint()
    val initial = j.toPattern()
    val result = LinkedHashSet<Conclusion>()
    for (a in ops.leaves(g)) {
        m.cancellation.checkpoint()
        restrict(initial, Conclusion(a.fact, a.exclusion, g.layer == Layer.DEMAND), d, m.marks, policy)?.let { result += it }
    }
    return result.toList()
}

/** Restrict protected memberships with the same geometry as the ordinary result. */
internal fun restrictFacts(ops: ApOps, j: InitialAp, g: Facts, d: DemandPattern,
                           policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = ops.manager.marks)): List<Facts> {
    val out = CollectingOut()
    ops.manager.transportProtection(g, out) { part, sink ->
        for (value in restrictPlainFacts(ops, j, part, d, policy)) sink.result(value)
    }
    return out.results
}

/** Exact-key packing preserves every reference leaf and its raw layer. */
private fun restrictPlainFacts(ops: ApOps, j: InitialAp, g: Facts, d: DemandPattern,
                           policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = ops.manager.marks)): List<Facts> {
    val m = ops.manager
    val values = LinkedHashMap<GroupKey, Facts>()
    for (selected in restrictRaw(ops, j, g, d, policy)) {
        val c = normalizeFlowSummaryConclusion(selected)
        m.cancellation.checkpoint()
        val f = m.factsOf(c.fact, c.exclusion, if (c.demand) Layer.DEMAND else Layer.NORMAL)
        val old = values[f.groupKey]
        values[f.groupKey] = if (old == null) f else m.mergeAddDelta(old, f).first
    }
    return values.values.toList()
}

/** Selection reads raw headers only. A transient native read view does not change them. */
internal fun selectDemand(m: ApManager, premise: PremiseKey, g: Facts, direction: Direction): Facts? {
    m.cancellation.checkpoint()
    if (g.layer == Layer.DEMAND) return g
    val j = premise as? InitialAp ?: return g
    if (direction == Direction.BACKWARD && j.isZero) return g
    return null
}
