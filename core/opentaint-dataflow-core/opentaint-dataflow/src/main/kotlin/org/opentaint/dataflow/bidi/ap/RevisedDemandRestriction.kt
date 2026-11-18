package org.opentaint.dataflow.bidi.ap

/** Dp comes from a previous executable premise, so it cannot have an NE tail. */
internal fun selectRevisedConclusion(candidate: Pattern, demand: Pattern, catalog: MarkTable): Pattern? {
    val d = normalizeDemandFieldExclusion(demand)
    if (candidate.fact.base != d.fact.base || !marksMeet(d.fact.mark, candidate.fact.mark, catalog) ||
        d.fact.tail == Tail.NON_EMPTY_MAY) return null
    val p = d.fact.path
    val q = candidate.fact.path
    val t = candidate.fact.tail
    fun select(tail: Tail, e: ExclusionSet = ExclusionSet.Empty): Pattern =
        Pattern(candidate.fact.copy(path = p, tail = tail), e)
    if (p == q) {
        return when (t) {
            Tail.EXACT, Tail.STAR -> candidate
            Tail.NON_EMPTY_MAY -> candidate.takeUnless { d.fact.tail == Tail.EXACT }
            Tail.ANY -> if (d.fact.tail == Tail.EXACT) select(Tail.EXACT) else candidate
            Tail.ANY_TAINT -> when (d.fact.tail) {
                Tail.EXACT -> select(Tail.EXACT, if (candidate.fact.mark is MarkSlot.Star) candidate.exclusion else ExclusionSet.Empty)
                Tail.STAR -> select(Tail.ANY_TAINT, candidate.exclusion.union(d.exclusion))
                else -> candidate
            }
        }
    }
    if (q.startsWith(p)) return candidate.takeIf { d.tailAdmits(q.drop(p.size)) }
    if (!p.startsWith(q) || !candidate.tailAdmits(p.drop(q.size))) return null
    return when (t) {
        Tail.EXACT -> null
        Tail.STAR -> candidate
        Tail.ANY, Tail.NON_EMPTY_MAY -> select(if (d.fact.tail == Tail.EXACT) Tail.EXACT else Tail.ANY)
        Tail.ANY_TAINT -> when (d.fact.tail) {
            Tail.EXACT -> select(Tail.EXACT)
            Tail.STAR -> select(Tail.ANY_TAINT, d.exclusion)
            else -> select(Tail.ANY_TAINT)
        }
    }
}
