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
        for (emitted in policy.emitAdmissions(d.entry, a, added.layer)) result += m.initial(emitted.pattern)
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

/** An accepted existing entry predicate, bound to immutable native patterns.
 * No hypothetical initial is interned and no caller may construct a ticket. */
internal class EntryRestrictionTicket private constructor(
    val initial: Pattern,
    val pair: DemandPattern,
    private val ops: ApOps,
) {
    fun acceptedOutput(): AcceptedEntryOutput? = AcceptedEntryOutput.from(this)

    fun restrict(raw: Facts): List<Facts> {
        val out = CollectingOut()
        ops.manager.transportProtection(raw, out) { part, sink ->
            val selected = LinkedHashSet<Conclusion>()
            for (leaf in ops.leaves(part)) {
                ops.manager.cancellation.checkpoint()
                restrictConclusionOnly(Conclusion(leaf.fact, leaf.exclusion, part.layer == Layer.DEMAND),
                    pair.exit, ops.manager.marks)?.let(selected::add)
            }
            for (value in packRestrictedSelections(ops, selected)) sink.result(value)
        }
        return out.results
    }

    companion object {
        fun prepare(ops: ApOps, initial: Pattern, pair: DemandPattern,
                    policy: RestrictedInitialPolicy): EntryRestrictionTicket? {
            ops.manager.cancellation.checkpoint()
            return if (policy.canStoreInitial(pair.entry, initial)) EntryRestrictionTicket(initial, pair, ops) else null
        }
    }
}

/** Only a successful native entry check can produce this DATA output capability. */
internal class AcceptedEntryOutput private constructor(
    val initial: Pattern, val pair: DemandPattern, val fullExit: Pattern,
) {
    companion object {
        fun from(ticket: EntryRestrictionTicket): AcceptedEntryOutput? =
            ticket.pair.exit?.let { AcceptedEntryOutput(ticket.initial, ticket.pair, it) }
    }
}

/** Exact-key packing preserves every reference leaf and its raw layer. */
private fun restrictPlainFacts(ops: ApOps, j: InitialAp, g: Facts, d: DemandPattern,
                           policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = ops.manager.marks)): List<Facts> {
    return packRestrictedSelections(ops, restrictRaw(ops, j, g, d, policy))
}

internal fun packRestrictedSelections(ops: ApOps, selected: Iterable<Conclusion>): List<Facts> {
    val m = ops.manager
    val values = LinkedHashMap<GroupKey, Facts>()
    for (value in selected) {
        val c = normalizeFlowSummaryConclusion(value)
        m.cancellation.checkpoint()
        val f = m.factsOf(c.fact, c.exclusion, if (c.demand) Layer.DEMAND else Layer.NORMAL)
        val old = values[f.groupKey]
        values[f.groupKey] = if (old == null) f else m.mergeAddDelta(old, f).first
    }
    return values.values.toList()
}

/** The existing handoff truth table, applied to final admitted headers. */
internal fun selectedForHandoff(premise: PremiseKey, layer: Layer, direction: Direction): Boolean {
    if (layer == Layer.DEMAND) return true
    val single = premise as? InitialAp ?: return true
    return direction == Direction.BACKWARD && single.isZero
}

internal fun selectDemand(m: ApManager, premise: PremiseKey, g: Facts, direction: Direction): Facts? {
    m.cancellation.checkpoint()
    return g.takeIf { selectedForHandoff(premise, it.layer, direction) }
}
