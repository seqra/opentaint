package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.*

/** Compatibility for assertions about the full relation. Production C2 does not enumerate these pairs. */
internal fun DemandStore.near(method: MethodKey, actual: Pattern): List<DemandPattern> {
    val stored = explicitRows(method).filter { nearLocation(it.entry, actual, false) }
    val completed = completion?.near(method, actual)?.toList().orEmpty()
    val implicit = when {
        actual.fact.base == AccessPathBase.Zero -> listOf(zeroDemand)
        hasSharedStaticCarry && actual.fact.base == STATIC -> guidancePattern(actual).let { listOf(DemandPattern(it, it)) }
        else -> emptyList()
    }
    return (stored + completed + implicit).distinct()
}

internal fun DemandStore.covering(method: MethodKey, initial: InitialAp): List<DemandPattern> {
    val actual = initial.toPattern()
    val stored = explicitRows(method).filter { nearLocation(it.entry, actual, true) }
    val completed = completion?.covering(method, initial)?.toList().orEmpty()
    val implicit = if (hasSharedStaticCarry && actual.fact.base == STATIC)
        guidancePattern(actual).let { listOf(DemandPattern(it, it)) } else emptyList()
    return (stored + completed + implicit).distinct()
}

internal fun FrozenCompletion.near(method: MethodKey, actual: Pattern): Sequence<DemandPattern> =
    referencePairs(method, actual, false)

internal fun FrozenCompletion.covering(method: MethodKey, initial: InitialAp): Sequence<DemandPattern> =
    referencePairs(method, initial.toPattern(), true)

private fun nearLocation(entry: Pattern, actual: Pattern, prefixesOnly: Boolean): Boolean =
    entry.fact.base == actual.fact.base && (actual.fact.path.startsWith(entry.fact.path) ||
        !prefixesOnly && entry.fact.path.startsWith(actual.fact.path))

/** Test-only exhaustive path enumeration, independent of optimized initial/existence lookups. */
private fun FrozenCompletion.referencePairs(method: MethodKey, actual: Pattern, prefixesOnly: Boolean): Sequence<DemandPattern> = sequence {
    val view = visible(method)
    val pending = ArrayDeque<StaticGuidanceEdge>()
    val seen = HashSet<StaticGuidanceEdge>()
    fun admit(edge: StaticGuidanceEdge) { if (seen.add(edge)) pending.addLast(edge) }
    for (edge in view.targets(actual, prefixesOnly)) admit(edge)
    while (pending.isNotEmpty()) {
        val edge = pending.removeFirst()
        yield(DemandPattern(edge.to, edge.from))
        if (edge.from.fact.base != STATIC) continue
        for (left in view.incoming(edge.from)) {
            // Candidate anchors are checked by exact first class/field markers as in the reference grammar.
            fun anchor(p: Pattern): List<Int> = p.fact.path.take(if (p.fact.path.size > 1) 2 else 1)
            if (anchor(left.to) != anchor(edge.from) || !overlap(left.to, edge.from)) continue
            val relation = when (val l = left.marks) {
                GuidanceMarks.Flow -> edge.marks
                is GuidanceMarks.Mapped -> when (val r = edge.marks) {
                    GuidanceMarks.Flow -> l
                    is GuidanceMarks.Mapped -> if (l.output == r.input) GuidanceMarks.Mapped(l.input, r.output) else continue
                }
            }
            val mapped = relation as? GuidanceMarks.Mapped
            fun endpoint(p: Pattern, mark: TaintMark?): Pattern = if (p.fact.base == AccessPathBase.Zero) p
                else p.copy(fact = p.fact.copy(mark = if (mapped == null) MarkSlot.STAR else MarkSlot.Concrete(checkNotNull(mark))))
            admit(StaticGuidanceEdge(endpoint(left.from, mapped?.input), endpoint(edge.to, mapped?.output), relation))
        }
    }
}
