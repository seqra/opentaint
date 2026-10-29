package org.opentaint.dataflow.bidi.ap

/** A complete summary pair has one canonical storage key. Point keys stay unchanged. */
data class FlowSummaryForm(val premise: PremiseKey, val facts: Facts)

fun normalizeFlowSummary(manager: ApManager, premise: PremiseKey, facts: Facts): FlowSummaryForm {
    if (!premise.isFlow || facts !is FlowTree) return FlowSummaryForm(premise, facts)
    val initial = premise as InitialAp
    val key = if (initial.tail == Tail.EXACT)
        manager.initial(initial.base, initial.path, Tail.STAR, initial.exclusion, initial.mark)
    else initial
    val result = if (facts.tail == Tail.EXACT)
        manager.flowTree(facts.base, facts.layer, facts.exclusion, facts.markExclusion, facts.root, Tail.STAR)
    else facts
    return FlowSummaryForm(key, result)
}

fun normalizeFlowSummaryConclusion(c: Conclusion): Conclusion =
    if (c.fact.mark is MarkSlot.Star && c.fact.tail == Tail.EXACT)
        c.copy(fact = c.fact.copy(tail = Tail.STAR)) else c

fun assertCanonicalFlowSummary(premise: PremiseKey, facts: Facts) {
    if (!premise.isFlow || facts !is FlowTree) return
    check((premise as InitialAp).tail != Tail.EXACT && facts.tail != Tail.EXACT) {
        "Normalize the complete FLOW pair before summary storage"
    }
}

/** Guidance comparisons use the same pair form as summaries. Raw writer keys stay raw. */
fun normalizeFlowSummaryPatterns(from: Pattern, to: Pattern): Pair<Pattern, Pattern> {
    if (from.fact.mark !is MarkSlot.Star || to.fact.mark !is MarkSlot.Star) return from to to
    fun normal(p: Pattern) = if (p.fact.tail == Tail.EXACT) p.copy(fact = p.fact.copy(tail = Tail.STAR)) else p
    return normal(from) to normal(to)
}
