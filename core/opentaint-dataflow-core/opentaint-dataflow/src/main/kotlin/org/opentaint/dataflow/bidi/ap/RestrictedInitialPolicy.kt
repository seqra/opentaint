package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor

/** One run's pure C2 policy. Image tests inspect templates; they never intern hypothetical facts. */
class RestrictedInitialPolicy(
    val run: Int = 2,
    val fieldLimit: Int = Int.MAX_VALUE,
    val direction: Direction = if (run % 2 == 0) Direction.BACKWARD else Direction.FORWARD,
    private val catalog: MarkTable? = null,
) {
    init { require(run >= 2 && fieldLimit >= 1) }

    fun emit(demand: Pattern, actual: Pattern): Pattern? {
        val d = normalizeDemandFieldExclusion(demand)
        if (d.fact.base != actual.fact.base || !markSub(d.fact.mark, actual.fact.mark, catalog)) return null
        if (!fitsBudget(d) || !fitsBudget(actual)) return null
        val p = d.fact.path
        val q = actual.fact.path
        val mark = boundMark(d.fact.mark, actual.fact.mark)
        fun result(path: List<Int>, tail: Tail, e: ExclusionSet = ExclusionSet.Empty): Pattern? {
            val value = Pattern(PathFact(d.fact.base, path, tail, mark), e)
            return value.takeIf(::legalInitial)
        }
        if (q == p) return when (d.fact.tail) {
            Tail.ANY -> when (actual.fact.tail) {
                Tail.STAR -> null
                Tail.EXACT -> result(p, Tail.EXACT)
                Tail.ANY -> result(p, Tail.ANY)
                Tail.ANY_TAINT -> result(p, Tail.ANY_TAINT, actual.exclusion)
            }
            Tail.STAR, Tail.EXACT -> result(p, Tail.EXACT)
            Tail.ANY_TAINT -> null // A demand entry never has a MUST tail.
        }
        if (q.startsWith(p)) {
            if (!d.tailAdmits(q.drop(p.size))) return null
            return when (d.fact.tail) {
                Tail.STAR -> if (run == 2) result(p, Tail.STAR, d.exclusion) else null
                Tail.ANY -> {
                    val end = firstFieldEnd(d.fact.base, p, q) ?: return null
                    val tail = if (mark is MarkSlot.Concrete && actual.fact.tail == Tail.EXACT && end == q.size)
                        Tail.EXACT else Tail.STAR
                    result(q.take(end), tail)
                }
                else -> null
            }
        }
        if (p.startsWith(q) && actual.tailAdmits(p.drop(q.size))) return when (d.fact.tail) {
            Tail.ANY -> when (actual.fact.tail) {
                Tail.ANY -> result(p, Tail.ANY)
                Tail.ANY_TAINT -> result(p, Tail.ANY_TAINT, d.exclusion)
                else -> null
            }
            Tail.STAR, Tail.EXACT -> result(p, Tail.EXACT)
            Tail.ANY_TAINT -> null
        }
        return null
    }

    /** Complete structural output image, including the non-idempotent run-2 requested STAR. */
    fun canEmitInitial(demand: Pattern, initial: Pattern): Boolean {
        val d = normalizeDemandFieldExclusion(demand)
        if (!legalInitial(initial) || !fitsBudget(d) || d.fact.base != initial.fact.base ||
            !renderedMark(d.fact.mark, initial.fact.mark)) return false
        val p = d.fact.path
        val q = initial.fact.path
        if (q == p) return when (initial.fact.tail) {
            Tail.EXACT -> initial.exclusion == ExclusionSet.Empty && d.fact.tail != Tail.ANY_TAINT
            Tail.ANY -> d.fact.tail == Tail.ANY && initial.exclusion == ExclusionSet.Empty
            Tail.ANY_TAINT -> d.fact.tail == Tail.ANY
            Tail.STAR -> run == 2 && d.fact.tail == Tail.STAR && initial.exclusion == d.exclusion &&
                p.count { it.isCounted() } < fieldLimit &&
                !(initial.fact.base == STATIC && p.size == 1)
        }
        if (d.fact.tail != Tail.ANY || !q.startsWith(p) || !d.tailAdmits(q.drop(p.size))) return false
        val end = firstFieldEnd(d.fact.base, p, q) ?: return false
        return end == q.size && initial.exclusion == ExclusionSet.Empty &&
            (initial.fact.tail == Tail.STAR || initial.fact.tail == Tail.EXACT && initial.fact.mark is MarkSlot.Concrete)
    }

    /** Summary keys are normalized, but the containment test belongs to their raw preimage. */
    fun canStoreInitial(entry: Pattern, stored: Pattern): Boolean {
        fun fits(raw: Pattern): Boolean = canEmitInitial(entry, raw) && insideDemand(raw, entry, catalog)
        if (fits(stored)) return true
        return stored.fact.mark is MarkSlot.Star && stored.fact.tail == Tail.STAR &&
            stored.exclusion == ExclusionSet.Empty && fits(stored.copy(fact = stored.fact.copy(tail = Tail.EXACT)))
    }

    private fun boundMark(required: MarkSlot, actual: MarkSlot): MarkSlot =
        if (required is MarkSlot.Concrete && catalog?.isGroup(required.mark) == true &&
            actual is MarkSlot.Concrete) actual else required

    private fun renderedMark(required: MarkSlot, rendered: MarkSlot): Boolean =
        if (required is MarkSlot.Star) rendered == required
        else rendered is MarkSlot.Concrete && markSub(required, rendered, catalog)

    private fun fitsBudget(p: Pattern): Boolean = p.fact.path.count { it.isCounted() } <= fieldLimit

    private fun legalInitial(p: Pattern): Boolean {
        if (!fitsBudget(p) || p.fact.tail == Tail.ANY_TAINT && direction == Direction.BACKWARD) return false
        if (p.fact.mark is MarkSlot.Concrete && catalog?.isGroup(p.fact.mark.mark) == true) return false
        if (p.fact.tail != Tail.STAR && p.fact.tail != Tail.ANY_TAINT && p.exclusion != ExclusionSet.Empty) return false
        if (p.fact.mark is MarkSlot.Star && !p.fact.mark.excluded.isEmpty) return false
        if (p.fact.base == AccessPathBase.Zero) return p.fact.path.isEmpty() && p.fact.tail == Tail.EXACT &&
            p.exclusion == ExclusionSet.Empty && p.fact.mark == MarkSlot.Concrete(TaintMark.ZERO)
        if (p.fact.base != STATIC || p.fact.mark is MarkSlot.Star) return true
        val path = p.fact.path
        return path.size == 1 && path[0].isClass() && p.fact.tail == Tail.EXACT ||
            path.size >= 2 && path[0].isClass() && path[1].isFieldAccessor()
    }

    /** A JVM static anchor is indivisible. A raw array element cannot become a class abstraction. */
    private fun firstFieldEnd(base: AccessPathBase, prefix: List<Int>, path: List<Int>): Int? {
        val index = (prefix.size until path.size).firstOrNull { path[it].isCounted() } ?: return null
        val end = index + 1
        if (base == STATIC && (end < 2 || !path[0].isClass() || !path[1].isFieldAccessor())) return null
        return end
    }
}
