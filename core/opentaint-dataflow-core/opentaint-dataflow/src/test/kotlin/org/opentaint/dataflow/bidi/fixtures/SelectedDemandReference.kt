package org.opentaint.dataflow.bidi.fixtures

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import org.opentaint.dataflow.bidi.ap.*

/** Scalar test oracle for the selected admission table. No production policy or candidate index is read. */
internal class SelectedDemandReference(
    private val run: Int,
    private val limit: Int,
    private val direction: Direction,
    private val marks: MarkTable,
    private val witnessField: Int,
) {
    private fun normalizeEntry(d: Pattern) = if (d.fact.tail == Tail.STAR && d.fact.mark is MarkSlot.Star)
        d.copy(exclusion = ExclusionSet.Empty) else d

    fun emit(demand: Pattern, actual: Pattern): Pattern? {
        val d = normalizeEntry(demand)
        if (d.fact.base != actual.fact.base || !markSub(d.fact.mark, actual.fact.mark, marks)) return null
        if (listOf(d, actual).any { it.fact.path.count { field -> field.isCounted() } > limit }) return null
        val mark = if (d.fact.mark is MarkSlot.Concrete && marks.isGroup(d.fact.mark.mark)) actual.fact.mark else d.fact.mark
        fun selected(path: List<Int>, tail: Tail, e: ExclusionSet = ExclusionSet.Empty): Pattern? {
            if (tail == Tail.ANY_TAINT && direction == Direction.BACKWARD) return null
            if (mark is MarkSlot.Concrete && marks.isGroup(mark.mark)) return null
            if (d.fact.base == AccessPathBase.Zero &&
                (path.isNotEmpty() || tail != Tail.EXACT || mark != MarkSlot.Concrete(TaintMark.ZERO))) return null
            if (mark is MarkSlot.Star && !mark.excluded.isEmpty) return null
            if (d.fact.base == STATIC && mark is MarkSlot.Concrete) {
                val field = path.size >= 2 && path[0].isClass() && path[1].isFieldAccessor()
                val marker = path.size == 1 && path[0].isClass() && tail == Tail.EXACT
                if (!field && !marker) return null
            }
            return Pattern(PathFact(d.fact.base, path, tail, mark), e)
        }
        val p = d.fact.path
        val q = actual.fact.path
        if (p == q) return when (d.fact.tail) {
            Tail.STAR, Tail.EXACT -> selected(p, Tail.EXACT)
            Tail.ANY -> when (actual.fact.tail) {
                Tail.EXACT -> selected(p, Tail.EXACT)
                Tail.ANY -> selected(p, Tail.ANY)
                Tail.ANY_TAINT -> selected(p, Tail.ANY_TAINT, actual.exclusion)
                Tail.STAR -> null
            }
            Tail.ANY_TAINT -> null
        }
        if (q.startsWith(p) && d.tailAdmits(q.drop(p.size))) {
            if (d.fact.tail == Tail.STAR) return if (run == 2) selected(p, Tail.STAR, d.exclusion) else null
            if (d.fact.tail != Tail.ANY) return null
            val first = (p.size until q.size).firstOrNull { q[it].isCounted() } ?: return null
            val chain = q.take(first + 1)
            if (d.fact.base == STATIC && (chain.size < 2 || !chain[0].isClass() || !chain[1].isFieldAccessor())) return null
            val exact = mark is MarkSlot.Concrete && actual.fact.tail == Tail.EXACT && chain == q
            return selected(chain, if (exact) Tail.EXACT else Tail.STAR)
        }
        if (p.startsWith(q) && actual.tailAdmits(p.drop(q.size))) return when (d.fact.tail) {
            Tail.STAR, Tail.EXACT -> selected(p, Tail.EXACT)
            Tail.ANY -> when (actual.fact.tail) {
                Tail.ANY -> selected(p, Tail.ANY)
                Tail.ANY_TAINT -> selected(p, Tail.ANY_TAINT, d.exclusion)
                else -> null
            }
            Tail.ANY_TAINT -> null
        }
        return null
    }

    /** Check the emitter image with explicit finite witness forms, then test raw containment. */
    fun stores(entry: Pattern, stored: Pattern): Boolean {
        val raw = buildList {
            add(stored)
            if (stored.fact.mark is MarkSlot.Star && stored.fact.tail == Tail.STAR && stored.exclusion == ExclusionSet.Empty)
                add(stored.copy(fact = stored.fact.copy(tail = Tail.EXACT)))
        }
        return raw.any { candidate ->
            if (!insideDemand(candidate, entry, marks)) return@any false
            val witnesses = listOf(candidate,
                candidate.copy(fact = candidate.fact.copy(tail = Tail.ANY), exclusion = ExclusionSet.Empty),
                candidate.copy(fact = candidate.fact.copy(path = candidate.fact.path + witnessField, tail = Tail.ANY),
                    exclusion = ExclusionSet.Empty))
            witnesses.any { emit(entry, it) == candidate }
        }
    }

    fun restrict(initial: Pattern, result: Conclusion, pair: DemandPattern): Conclusion? {
        if (!stores(pair.entry, initial)) return null
        val exit = normalizeEntry(pair.exit ?: return null)
        if (result.fact.base != exit.fact.base || !marksMeet(exit.fact.mark, result.fact.mark, marks)) return null
        val p = exit.fact.path
        val q = result.fact.path
        val raw = when {
            p == q -> when {
                result.fact.tail.isAny && exit.fact.tail == Tail.EXACT -> result.copy(
                    fact = result.fact.copy(tail = Tail.EXACT),
                    exclusion = if (result.fact.mark is MarkSlot.Star && result.fact.tail == Tail.ANY_TAINT)
                        result.exclusion else ExclusionSet.Empty)
                result.fact.tail == Tail.ANY_TAINT && exit.fact.tail == Tail.STAR ->
                    result.copy(exclusion = result.exclusion.union(exit.exclusion))
                else -> result
            }
            q.startsWith(p) -> result.takeIf { exit.tailAdmits(q.drop(p.size)) }
            p.startsWith(q) -> when (result.fact.tail) {
                Tail.EXACT -> null
                Tail.STAR -> result.takeIf { result.exclusion.admits(p.drop(q.size)) }
                Tail.ANY, Tail.ANY_TAINT -> if (!result.exclusion.admits(p.drop(q.size))) null
                    else if (exit.fact.tail == Tail.EXACT) result.copy(fact = result.fact.copy(path = p, tail = Tail.EXACT),
                        exclusion = ExclusionSet.Empty)
                    else result.copy(fact = result.fact.copy(path = p), exclusion =
                        if (result.fact.tail == Tail.ANY_TAINT && exit.fact.tail == Tail.STAR) exit.exclusion else ExclusionSet.Empty)
            }
            else -> null
        } ?: return null
        return if (initial.fact.mark is MarkSlot.Star && raw.fact.mark is MarkSlot.Star && raw.fact.tail == Tail.EXACT)
            raw.copy(fact = raw.fact.copy(tail = Tail.STAR)) else raw
    }
}
