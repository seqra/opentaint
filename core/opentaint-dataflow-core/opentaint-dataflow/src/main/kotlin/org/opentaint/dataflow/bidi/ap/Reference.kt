package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx

/** Scalar reference geometry for ordinary and FLOW query tails. */
data class PathFact(val base: AccessPathBase, val path: List<AccessorIdx>, val tail: Tail, val mark: MarkSlot)
data class Pattern(val fact: PathFact, val exclusion: ExclusionSet)

data class Conclusion(val fact: PathFact, val exclusion: ExclusionSet, val demand: Boolean) {
    init {
        check(fact.tail != Tail.ANY || demand) { "W6: a may conclusion must be DEMAND" }
        check(exclusion == ExclusionSet.Empty || fact.tail == Tail.STAR || fact.tail == Tail.ANY_TAINT ||
            (fact.tail == Tail.EXACT && fact.mark is MarkSlot.Star)) {
            "Only a STAR or must conclusion can exclude fields"
        }
    }
}


fun <T> List<T>.startsWith(p: List<T>): Boolean = size >= p.size && subList(0, p.size) == p

val STATIC: AccessPathBase = AccessPathBase.ClassStatic



data class DemandPattern(val entry: Pattern, val exit: Pattern?)

fun tailAdmits(tail: Tail, exclusion: ExclusionSet, r: List<AccessorIdx>): Boolean = when (tail) {
    Tail.STAR, Tail.ANY_TAINT -> exclusion.admits(r)   // r = [] or the first accessor of r is not excluded
    Tail.ANY -> true
    Tail.EXACT -> r.isEmpty()
}
fun Pattern.tailAdmits(r: List<AccessorIdx>) = tailAdmits(fact.tail, exclusion, r)

fun markSub(i: MarkSlot, c: MarkSlot, catalog: MarkTable? = null): Boolean = when (i) {
    is MarkSlot.Star -> when (c) {
        is MarkSlot.Star -> i.excluded.isSubsetOf(c.excluded)   // *∖X ⊇ *∖Y if and only if X ⊆ Y; * ⊇ every abstract mark
        is MarkSlot.Concrete -> c.mark !in i.excluded
    }
    is MarkSlot.Concrete -> c is MarkSlot.Concrete && (catalog?.coversAtom(i.mark, c.mark) ?: (c.mark == i.mark))
}

private fun tailSub(i: Pattern, c: Pattern): Boolean = when (i.fact.tail) {
    Tail.ANY -> true
    Tail.EXACT -> c.fact.tail == Tail.EXACT
    Tail.STAR, Tail.ANY_TAINT -> when (c.fact.tail) {       // the exclusion of i must exclude only what c excludes
        Tail.EXACT -> true
        Tail.ANY -> i.exclusion == ExclusionSet.Empty
        Tail.STAR, Tail.ANY_TAINT -> i.exclusion.isSubsetOf(c.exclusion)
    }
}

fun covers(i: Pattern, c: Pattern, catalog: MarkTable? = null): Boolean {
    if (i.fact.base != c.fact.base || !markSub(i.fact.mark, c.fact.mark, catalog)) return false
    val p = i.fact.path
    val q = c.fact.path
    if (!q.startsWith(p)) return false
    return if (q.size == p.size) tailSub(i, c) else i.tailAdmits(q.drop(p.size))
}

fun overlap(a: Pattern, b: Pattern): Boolean {
    if (a.fact.base != b.fact.base) return false
    val p = a.fact.path
    val q = b.fact.path
    return when {
        q.startsWith(p) -> a.tailAdmits(q.drop(p.size))
        p.startsWith(q) -> b.tailAdmits(p.drop(q.size))
        else -> false
    }
}

fun applicable(j: Pattern, a: Pattern, catalog: MarkTable? = null): Boolean =
    covers(j, a, catalog) && (!j.fact.tail.isAny || a.fact.tail.isAny)

fun inside(j: Pattern, a: Pattern, catalog: MarkTable? = null): Boolean =
    covers(a.copy(fact = a.fact.copy(mark = MarkSlot.Star(MarkSet.EMPTY))), j, catalog) && markSub(j.fact.mark, a.fact.mark, catalog)

/** Transient native-record read. Never emitted, started, interned as an InitialAp, or persisted. */
data class RecordLeafView(val premise: Pattern, val result: Conclusion)

fun summaryEdge(j: Pattern, g: Conclusion): PathEdge {
    val jOwn = j.fact.tail == Tail.ANY_TAINT
    val gOwn = g.fact.tail == Tail.ANY_TAINT
    return PathEdge(j.fact, g.fact,
        (if (jOwn) ExclusionSet.Empty else j.exclusion).union(if (gOwn) ExclusionSet.Empty else g.exclusion),
        fromExclusion = if (jOwn) j.exclusion else ExclusionSet.Empty,
        toExclusion = if (gOwn) g.exclusion else ExclusionSet.Empty)
}

/** Concrete native must views retain their existing policy. New FLOW must views always return an ANY demand. */
private fun mustRecordReadView(p: Pattern, g: Conclusion): RecordLeafView? {
    if (!g.demand && p.fact.mark is MarkSlot.Star && g.fact.mark is MarkSlot.Star &&
        ((p.fact.tail == Tail.ANY_TAINT && g.fact.tail in setOf(Tail.STAR, Tail.ANY_TAINT)) ||
            (p.fact.tail == Tail.STAR && g.fact.tail == Tail.ANY_TAINT))) {
        return RecordLeafView(Pattern(g.fact.copy(tail = Tail.STAR, mark = p.fact.mark), g.exclusion),
            Conclusion(p.fact.copy(tail = Tail.ANY, mark = g.fact.mark), ExclusionSet.Empty, demand = true))
    }
    val concrete = p.fact.mark is MarkSlot.Concrete && g.fact.mark is MarkSlot.Concrete
    val accepted = !g.demand && concrete && when (p.fact.tail) {
        Tail.EXACT -> p.exclusion == ExclusionSet.Empty && g.fact.tail == Tail.ANY_TAINT
        Tail.ANY_TAINT -> g.fact.tail == Tail.ANY_TAINT ||
            (g.fact.tail == Tail.EXACT && g.exclusion == ExclusionSet.Empty)
        else -> false
    }
    if (!accepted) return null
    val readPremise = if (g.fact.tail == Tail.ANY_TAINT)
        Pattern(g.fact.copy(tail = Tail.STAR), g.exclusion)          // retain the old conclusion E and concrete mark
    else Pattern(g.fact, ExclusionSet.Empty)                        // exact conclusion stays exact
    val demand = p.fact.tail == Tail.ANY_TAINT
    val resultFact = if (demand) p.fact.copy(tail = Tail.ANY) else p.fact
    return RecordLeafView(readPremise, Conclusion(resultFact, ExclusionSet.Empty, demand))   // forget old must-input E
}

/** Raw normal singleton record only. CurrentSimplifications.MustViews.readView_factored_equiv checks the accepted
 *  must constructor. Retain generic micro-edge revEdge and its fallback guards for every other native shape. */
fun reverseRecordLeaf(direction: Direction, p: Pattern, g: Conclusion): RecordLeafView? {
    if (g.demand) return null
    if (p.exclusion != ExclusionSet.Empty && p.fact.tail != Tail.STAR && p.fact.tail != Tail.ANY_TAINT) return null
    if (direction == Direction.BACKWARD && (p.fact.tail == Tail.ANY_TAINT || g.fact.tail == Tail.ANY_TAINT)) return null
    if (direction == Direction.FORWARD) mustRecordReadView(p, g)?.let { return it }
    if (p.fact.tail == Tail.ANY_TAINT) return null                   // no unsupported native must-input fallback
    if (p.fact.tail == Tail.STAR && p.fact.mark is MarkSlot.Concrete) return null   // invalid native normal shape
    val rev = revEdge(summaryEdge(p, g)) ?: return null
    return RecordLeafView(Pattern(rev.from, ExclusionSet.Empty),
        Conclusion(rev.to, rev.exclusion, demand = rev.to.tail == Tail.ANY))
}

/** Identity classification without starting a transient premise. Concrete STAR readers are effects. */
fun recordLeafIdentity(v: RecordLeafView): Boolean = !v.result.demand && v.premise.fact.base != AccessPathBase.Zero &&
    (v.premise.fact.tail == Tail.EXACT || (v.premise.fact.tail == Tail.STAR && v.premise.fact.mark is MarkSlot.Star)) &&
    v.result.fact == v.premise.fact && v.result.exclusion == v.premise.exclusion


fun meet(a: Pattern, d: Pattern): Pair<Tail, ExclusionSet> {
    return when {
        a.fact.tail == Tail.ANY_TAINT && d.fact.tail == Tail.STAR ->
            Tail.ANY_TAINT to a.exclusion.union(d.exclusion)
        a.fact.tail.isAny && d.fact.tail.isAny -> a.fact.tail to a.exclusion
        a.fact.tail.isAny -> d.fact.tail to d.exclusion
        d.fact.tail.isAny -> a.fact.tail to a.exclusion
        a.fact.tail == Tail.EXACT || d.fact.tail == Tail.EXACT -> Tail.EXACT to ExclusionSet.Empty
        else -> Tail.STAR to a.exclusion.union(d.exclusion)
    }
}

/** Demand-only widening. Actual facts, native records and concrete demand retain field E. */
fun normalizeDemandFieldExclusion(pattern: Pattern): Pattern =
    if (pattern.fact.mark is MarkSlot.Star && pattern.fact.tail == Tail.STAR &&
        pattern.exclusion != ExclusionSet.Empty) pattern.copy(exclusion = ExclusionSet.Empty)
    else pattern

/** Scalar table view, including forward uniform templates. The engine passes its run policy explicitly. */
fun emit(d: Pattern, a: Pattern, catalog: MarkTable? = null): Pattern? =
    RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = catalog).emit(d, a)

fun flowForm(d: Pattern): Pattern {
    val star = MarkSlot.Star(MarkSet.EMPTY)
    return if (d.fact.tail == Tail.ANY) Pattern(d.fact.copy(tail = Tail.STAR, mark = star), ExclusionSet.Empty)
    else Pattern(d.fact.copy(mark = star), d.exclusion)                // `STAR/E` keeps E
}

fun commonPart(d: Pattern, a: Pattern, catalog: MarkTable? = null): Pattern? {
    if (d.fact.base != a.fact.base) return null
    // a T demand needs the mark T: an abstract `a` gives nothing ("the added fact can't satisfy the demand", F72);
    // `*` admits every mark (Lean: markMatchB; with no `*∖X` pattern it is markSub)
    if (!markSub(d.fact.mark, a.fact.mark, catalog)) return null
    val p = d.fact.path
    val q = a.fact.path
    return when {
        q.size > p.size && q.startsWith(p) ->                                   // below: the fact itself
            if (d.tailAdmits(q.drop(p.size))) a else null
        q == p -> {                                                              // at: the meet of the tails
            val (tail, excl) = meet(a, d)
            Pattern(a.fact.copy(tail = tail), excl)
        }
        p.startsWith(q) ->                                    // above: the demand chain, the meet of the tails
            if (a.tailAdmits(p.drop(q.size))) {
                // E excludes first accessors at q. After the admitted descent to p it has no effect there.
                // Keep the demand's own E at p, including the MUST/STAR and correlated STAR cells.
                val (tail, excl) = meet(a.copy(exclusion = ExclusionSet.Empty), d)
                Pattern(d.fact.copy(tail = tail, mark = a.fact.mark), excl)
            } else null
        else -> null
    }
}

fun satisfies(j: Pattern, a: Pattern, restricted: Boolean): Boolean {
    if (j.fact.tail == Tail.ANY_TAINT && j.fact.mark is MarkSlot.Star)
        return a.fact.tail == Tail.ANY_TAINT && markSub(j.fact.mark, a.fact.mark) &&
            covers(a.copy(fact = a.fact.copy(mark = MarkSlot.STAR)), j.copy(fact = j.fact.copy(mark = MarkSlot.STAR)))
    return if (!restricted) applicable(j, a) || inside(j, a)
    else if (j.fact.tail == Tail.STAR && j.exclusion == ExclusionSet.Empty && j.fact.mark == MarkSlot.STAR)
        overlap(j, a)
    else inside(j, a) || ((j.fact.mark == MarkSlot.STAR || j.fact.tail == Tail.STAR) && applicable(j, a))
}

fun recordDemand(j: Pattern, a: Pattern, resultDemand: Boolean): Boolean =
    resultDemand || (j.fact.tail == Tail.ANY_TAINT && !inside(j, a))
fun insideLoc(j: Pattern, d: Pattern): Boolean {
    val star = MarkSlot.Star(MarkSet.EMPTY)
    return covers(d.copy(fact = d.fact.copy(mark = star)), j.copy(fact = j.fact.copy(mark = star)))
}

fun insideDemand(j: Pattern, d: Pattern, catalog: MarkTable? = null): Boolean {
    val entry = normalizeDemandFieldExclusion(d)
    return insideLoc(j, entry) && markSub(entry.fact.mark, j.fact.mark, catalog)
}

fun marksMeet(dp: MarkSlot, c: MarkSlot, catalog: MarkTable? = null): Boolean = when {
    dp is MarkSlot.Concrete && c is MarkSlot.Concrete -> (catalog?.let { it.coversAtom(dp.mark, c.mark) || it.coversAtom(c.mark, dp.mark) } ?: (dp.mark == c.mark))
    dp is MarkSlot.Concrete -> dp.mark !in (c as MarkSlot.Star).excluded      // an abstract conclusion stays as it is
    c is MarkSlot.Concrete -> c.mark !in (dp as MarkSlot.Star).excluded
    else -> true
}

fun meetConclusion(sc: Conclusion, dp: Pattern): Conclusion = when {
    !sc.fact.tail.isAny -> sc                                     // `$`; `*` stays whole (a FLOW conclusion, F72)
    dp.fact.tail == Tail.EXACT -> sc.copy(fact = sc.fact.copy(tail = Tail.EXACT),
        exclusion = if (sc.fact.mark is MarkSlot.Star && sc.fact.tail == Tail.ANY_TAINT) sc.exclusion else ExclusionSet.Empty)
    sc.fact.tail == Tail.ANY_TAINT && dp.fact.tail == Tail.STAR -> sc.copy(exclusion = sc.exclusion.union(dp.exclusion))
    else -> sc                                                    // `[any] ∩ STAR/E2` (the exception), `∩ [any]`
}

fun restrict(sp: Pattern, sc: Conclusion, d: DemandPattern, catalog: MarkTable? = null,
             policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = catalog)): Conclusion? {
    if (!policy.canStoreInitial(d.entry, sp)) return null
    return restrictConclusionOnly(sc, d.exit, catalog)
}

fun restrictConclusionOnly(sc: Conclusion, exit: Pattern?, catalog: MarkTable? = null): Conclusion? {
    val dp = normalizeDemandFieldExclusion(exit ?: return null)
    if (!marksMeet(dp.fact.mark, sc.fact.mark, catalog)) return null  // the mark of the conclusion meets the mark of D-p
    if (sc.fact.base != dp.fact.base) return null
    val p = dp.fact.path
    val q = sc.fact.path
    return when {
        q == p -> meetConclusion(sc, dp)                                         // at D-p: the meet
        q.startsWith(p) -> if (dp.tailAdmits(q.drop(p.size))) sc else null     // below D-p: keeps E
        p.startsWith(q) -> when (sc.fact.tail) {                                // above D-p
            Tail.ANY, Tail.ANY_TAINT ->
                if (!sc.exclusion.admits(p.drop(q.size))) null                   // E of `[any-taint]/E` (W8)
                else if (dp.fact.tail == Tail.EXACT)                             // the chain of D-p, the layer stays
                    sc.copy(fact = sc.fact.copy(path = p, tail = Tail.EXACT), exclusion = ExclusionSet.Empty)
                else sc.copy(fact = sc.fact.copy(path = p),
                    exclusion = if (sc.fact.tail == Tail.ANY_TAINT && dp.fact.tail == Tail.STAR) dp.exclusion
                                else ExclusionSet.Empty)                         // [any-taint]/E2 under STAR/E2 (W8)
            Tail.STAR -> if (sc.exclusion.admits(p.drop(q.size))) sc else null   // a FLOW conclusion (F72)
            else -> null                                                         // `$`: no common location
        }
        else -> null
    }
}

data class PathEdge(val from: PathFact, val to: PathFact, val exclusion: ExclusionSet,
                    val fromExclusion: ExclusionSet = ExclusionSet.Empty,     // Ej of a must-premise (a summary, a record)
                    val toExclusion: ExclusionSet = ExclusionSet.Empty) {     // Et of an `[any-taint]/Et` summary conclusion
    @Volatile internal var compiled: CompiledEdge? = null
}

private fun PathEdge.premiseAdmits(r: List<AccessorIdx>): Boolean = when (from.tail) {
    Tail.EXACT -> r.isEmpty()
    Tail.ANY_TAINT -> fromExclusion.admits(r)   // a must-premise: Ej
    else -> exclusion.admits(r)        // `*`: E; `[any]`: E is Empty unless the target is `*` (row 1)
}

private class Shape(val path: List<AccessorIdx>, val tail: Tail, val exclusion: ExclusionSet, val demand: Boolean)

private fun below(c: Conclusion, edge: PathEdge, r: List<AccessorIdx>): Shape? {
    if (!edge.premiseAdmits(r)) return null
    val to = edge.to
    if (to.tail == Tail.STAR && r.isNotEmpty() && !edge.exclusion.admits(r)) return null
    return when (to.tail) {
        Tail.STAR -> when {
            r.isNotEmpty() -> Shape(to.path + r, c.fact.tail, c.exclusion, demand = false)   // keeps Ec (W8)
            c.fact.tail == Tail.EXACT -> Shape(to.path, Tail.EXACT,
                if (c.fact.mark is MarkSlot.Star) c.exclusion.union(edge.exclusion) else ExclusionSet.Empty, false)
            c.fact.tail == Tail.ANY -> Shape(to.path, Tail.ANY, ExclusionSet.Empty, demand = true)   // W6
            else -> Shape(to.path, c.fact.tail, c.exclusion.union(edge.exclusion), false)  // `STAR/Ec`, or the exclusion
        }                                                                                 // edge on `[any-taint]/Ec` (W8)
        Tail.ANY -> Shape(to.path, Tail.ANY, ExclusionSet.Empty, demand = true)               // W6: a may
        Tail.ANY_TAINT, Tail.EXACT -> Shape(to.path, to.tail,                                  // a must, or `$`
            if (to.tail == Tail.ANY_TAINT) edge.toExclusion else ExclusionSet.Empty,           // Et (W8)
            demand = false)        // W2 and the concrete premise gate reject STAR input; geometry still precedes that gate
    }
}

private fun PathEdge.isExcludedIdentityKeep(): Boolean =
    from.base == to.base && from.path == to.path && from.tail == Tail.STAR &&
        to.tail == Tail.STAR && exclusion != ExclusionSet.Empty

private fun above(c: Conclusion, edge: PathEdge, r: List<AccessorIdx>): Shape? {
    val admitted = when (c.fact.tail) {
        Tail.STAR, Tail.ANY_TAINT -> c.exclusion.admits(r); Tail.ANY -> true; Tail.EXACT -> false
    }
    if (!admitted) {
        // An excluded identity keep is the existing field-write effect, not a read.
        if (c.fact.tail == Tail.EXACT && c.fact.mark is MarkSlot.Star && edge.isExcludedIdentityKeep() && c.exclusion.admits(r))
            return Shape(edge.to.path, Tail.ANY, ExclusionSet.Empty, demand = true)
        return null
    }
    val to = edge.to
    if (c.fact.tail != Tail.ANY_TAINT) {           // a `*` fact loses its correlation; an `[any]` fact is demand (W6)
        val tail = if (to.tail == Tail.EXACT) Tail.EXACT else Tail.ANY
        return Shape(to.path, tail, ExclusionSet.Empty, demand = true)
    }
    return when (to.tail) {                        // every admitted location of c carries its mark: nothing is lost
        Tail.EXACT -> Shape(to.path, Tail.EXACT,
            if (c.fact.mark is MarkSlot.Star && r.isEmpty()) c.exclusion else ExclusionSet.Empty, demand = false)
        Tail.ANY_TAINT -> Shape(to.path, Tail.ANY_TAINT, edge.toExclusion, demand = false)    // Et
        Tail.ANY -> Shape(to.path, Tail.ANY, ExclusionSet.Empty, demand = true)               // W6: a may
        Tail.STAR -> Shape(to.path, Tail.ANY_TAINT, edge.exclusion, demand = false)          // the edge exclusion (W8)
    }
}

sealed interface EdgeOutcome {
    data object None : EdgeOutcome
    data class Fact(val conclusion: Conclusion) : EdgeOutcome
    data class Request(val mark: TaintMark) : EdgeOutcome                  // run 1 only (§4.5)
    data class PositionRequest(val path: List<AccessorIdx>) : EdgeOutcome     // run 1 only (§4.10 item 1)
}

fun rootOrClass(q: List<AccessorIdx>): Boolean = q.isEmpty() || (q.size == 1 && q[0].isClass())

fun concat(c: Conclusion, edge: PathEdge, edgeDemand: Boolean = false,
           staticIdentity: Boolean = false, restricted: Boolean = false, run1: Boolean = false): EdgeOutcome {
    val from = edge.from
    check(from.mark !is MarkSlot.Star || from.mark.excluded.isEmpty)          // S7
    check(edge.to.mark !is MarkSlot.Concrete || from.mark is MarkSlot.Concrete)          // S7
    check(from.tail != Tail.EXACT || edge.to.tail != Tail.STAR || from.mark is MarkSlot.Star)
    check(edge.to.tail != Tail.ANY_TAINT || edge.to.mark is MarkSlot.Concrete || from.mark is MarkSlot.Star)
    if (c.fact.base != from.base) return EdgeOutcome.None
    val p = from.path
    val q = c.fact.path
    val isAbove = p.size > q.size && p.startsWith(q)
    val shape = when {
        q.startsWith(p) -> below(c, edge, q.drop(p.size))
        isAbove -> above(c, edge, p.drop(q.size))
        else -> null
    } ?: return EdgeOutcome.None
    if (staticIdentity && from.base == STATIC && isAbove && rootOrClass(q)) {   // the static exception (§4.10)
        check(!restricted)
        return EdgeOutcome.PositionRequest(p.take(2))                          // cut to the static field or class
    }
    val premiseMark = from.mark
    if (premiseMark is MarkSlot.Concrete) {                                   // step 4: the mark gate
        when (val cm = c.fact.mark) {
            is MarkSlot.Concrete -> if (cm.mark != premiseMark.mark) return EdgeOutcome.None
            is MarkSlot.Star -> {
                if (premiseMark.mark in cm.excluded) return EdgeOutcome.None
                if (restricted) return EdgeOutcome.None                       // F72: no request after run 1 (§4.5)
                return EdgeOutcome.Request(premiseMark.mark)
            }
        }
    }
    val mark = compose(edge.to.mark, c.fact.mark) ?: return EdgeOutcome.None  // step 5
    val cover = run1 && shape.exclusion != ExclusionSet.Empty
    return EdgeOutcome.Fact(normalize(PathFact(edge.to.base, shape.path, shape.tail, mark),
        if (cover) ExclusionSet.Empty else shape.exclusion, c.demand || edgeDemand || shape.demand || cover))
}

fun compose(to: MarkSlot, c: MarkSlot): MarkSlot? = when (to) {
    is MarkSlot.Concrete -> to
    is MarkSlot.Star -> when (c) {
        is MarkSlot.Star -> MarkSlot.Star(to.excluded + c.excluded)
        is MarkSlot.Concrete -> if (c.mark in to.excluded) null else c
    }
}

fun normalize(f: PathFact, exclusion: ExclusionSet, demand: Boolean): Conclusion = when {
    demand && f.mark is MarkSlot.Star && (f.tail == Tail.EXACT || f.tail == Tail.ANY_TAINT) ->
        Conclusion(f.copy(tail = Tail.ANY), ExclusionSet.Empty, demand = true)
    f.tail == Tail.ANY -> Conclusion(f, ExclusionSet.Empty, demand = true)                                  // W6
    f.tail == Tail.ANY_TAINT -> {
        Conclusion(f, exclusion, demand)
    }
    else -> Conclusion(f, if (f.tail == Tail.EXACT && f.mark is MarkSlot.Concrete) ExclusionSet.Empty else exclusion, demand)
}

/** ap.md §6.5 (Lean startFact; a must-premise: AnyTaint.startT, with the exclusion AnyTaintEx.startX). No direction
 *  parameter: a must-premise occurs only in a forward restricted run (A1), and no other row reads the run. */
fun startFact(i: Pattern): Conclusion = when (i.fact.tail) {
    Tail.STAR -> Conclusion(i.fact, i.exclusion, demand = i.fact.mark is MarkSlot.Concrete)
    Tail.ANY -> Conclusion(i.fact, ExclusionSet.Empty, demand = true)
    Tail.ANY_TAINT -> Conclusion(i.fact, i.exclusion, demand = false)                // a must-premise: itself, normal
    Tail.EXACT -> Conclusion(i.fact, ExclusionSet.Empty, demand = false)
}

/** ap.md §4.4 (Lean cutPath, limitF; with the exclusion AnyTaintEx.limitFX). An `[any-taint]/E` fact over the limit
 *  becomes `[any]` in the demand layer and loses E (W8, A2). */
fun limit(c: Conclusion, fieldLimit: Int): Conclusion {
    require(fieldLimit >= 1) { "The field limit must be positive" }
    var n = 0
    for ((k, a) in c.fact.path.withIndex())
        if (a.isCounted() && ++n > fieldLimit)
            return Conclusion(c.fact.copy(path = c.fact.path.take(k), tail = Tail.ANY), ExclusionSet.Empty, demand = true)
    return c
}

enum class Pos { INSIDE, DISJOINT, PART }

/** ap.md §4.7 (Lean cleanPos; with the exclusion AnyTaintEx.cleanPosX: a cleaner strictly below an `[any-taint]/E` fact
 *  through an accessor in E is `disjoint`). The tree form is cleanPosAt (Part I §5.6). */
fun cleanPos(cl: Cleaner, c: PathFact, exclusion: ExclusionSet): Pos {
    if (c.base != cl.base) return Pos.DISJOINT
    val p = cl.path?.toList().orEmpty()
    val q = c.path
    return when {
        q.size > p.size && q.startsWith(p) -> if (cl.reach == CleanReach.EXACT) Pos.DISJOINT else Pos.INSIDE
        q == p -> when {
            cl.reach == CleanReach.AT_AND_BELOW -> Pos.INSIDE
            c.tail == Tail.EXACT -> if (cl.reach == CleanReach.EXACT) Pos.INSIDE else Pos.DISJOINT
            else -> Pos.PART
        }
        p.startsWith(q) -> when (c.tail) {
            Tail.EXACT -> Pos.DISJOINT
            Tail.STAR, Tail.ANY, Tail.ANY_TAINT ->                                  // `[any]`: the Empty exclusion admits
                if (exclusion.admits(p.drop(q.size))) Pos.PART else Pos.DISJOINT
        }
        else -> Pos.DISJOINT
    }
}

class CleanOut(val facts: List<Conclusion>, val request: TaintMark?)

/** ap.md §4.7, F75 selected-mark split (BaseCleaner.cleanRes); concrete/all-marks rows keep concPart. */
fun cleanRes(cl: Cleaner, c: Conclusion, run1: Boolean = false): CleanOut {
    val raw = if (run1 && c.fact.base == STATIC && cl.base == STATIC &&
        c.fact.mark is MarkSlot.Star && cl.mark != null && cleanPos(cl, c.fact, c.exclusion) == Pos.DISJOINT)
        CleanOut(listOf(c), null) else cleanResRaw(cl, c)
    return if (!run1) raw else CleanOut(raw.facts.map { value ->
        if (value.exclusion == ExclusionSet.Empty) value
        else value.copy(exclusion = ExclusionSet.Empty, demand = true)
    }, raw.request)
}

private fun cleanResRaw(cl: Cleaner, c: Conclusion): CleanOut {
    if (c.fact.base != cl.base) return CleanOut(listOf(c), null)
    val abstractMark = c.fact.mark as? MarkSlot.Star
    val selected = cl.mark
    if (abstractMark != null && selected != null)
        return CleanOut(listOf(c.copy(fact = c.fact.copy(mark = MarkSlot.Star(abstractMark.excluded + selected)))), selected)
        // The caller records this request only in run 1. Do not test the path or T ∈ X first.
    if (abstractMark != null && selected == null) {
        return CleanOut(wholeFlowClean(cl, c), null)
    }
    val pos = cleanPos(cl, c.fact, c.exclusion)
    if (pos == Pos.DISJOINT) return CleanOut(listOf(c), null)
    return when (val mk = c.fact.mark) {
        is MarkSlot.Concrete ->
            if (cl.mark != null && cl.mark != mk.mark) CleanOut(listOf(c), null)                  // T' not cleaned
            else if (pos == Pos.INSIDE) CleanOut(emptyList(), null)
            else CleanOut(concPart(cl, c), null)                                                  // one or two facts (A2)
        is MarkSlot.Star -> {
            check(cl.mark == null)                                               // selected mark handled before cleanPos
            CleanOut(if (pos == Pos.INSIDE) emptyList() else listOf(normalize(c.fact, c.exclusion, demand = true)), null)
        }
    }
}

/** Whole-position FLOW kill. Retain one uncertain inner residual, which covers deeper ones. */
internal fun wholeFlowClean(cl: Cleaner, c: Conclusion): List<Conclusion> {
    val path = cl.path?.toList().orEmpty()
    val q = c.fact.path
    if (q.startsWith(path)) return emptyList()
    if (!path.startsWith(q) || !c.exclusion.admits(path.drop(q.size))) return listOf(c)
    if (c.fact.tail == Tail.ANY) return listOf(c)
    val result = ArrayList<Conclusion>()
    result += c.copy(exclusion = c.exclusion.union(ExclusionSet.of(path[q.size])))
    if (q.size + 1 < path.size) {
        if (c.fact.tail == Tail.ANY_TAINT) {
            for (depth in q.size + 1 until path.size)
                result += c.copy(fact = c.fact.copy(path = path.take(depth)), exclusion = ExclusionSet.of(path[depth]))
        } else result += c.copy(fact = c.fact.copy(path = path.take(q.size + 1), tail = Tail.ANY),
            exclusion = ExclusionSet.Empty, demand = true)
    }
    return result
}

/** ap.md §4.7 (Lean concPart; with the exclusion AnyTaintEx.partX): a normal `[any-taint]/E` fact at x.p and a cleaner ONE
 *  accessor below it, at x.p.f: `atAndBelow` gives the fact with `E ∪ {f}`, `below` gives it and `(x, p.f, $, T)`, in
 *  the layer of c (A2). An any-tail fact at x.p under a `below` cleaner AT x.p keeps `(x, p, $, T)` in its layer. Any
 *  other `part` result (the `exact` cleaner one accessor below too) goes to the demand layer: an `[any-taint]` fact as
 *  `[any]`, with no exclusion (W8). */
fun concPart(cl: Cleaner, c: Conclusion): List<Conclusion> {
    val p = cl.path?.toList().orEmpty()
    val q = c.fact.path
    if (c.fact.tail == Tail.ANY_TAINT && p.size == q.size + 1 && p.startsWith(q) && cl.reach != CleanReach.EXACT) {
        val kept = c.copy(exclusion = c.exclusion.union(ExclusionSet.of(p.last())))          // `[any-taint]/(E ∪ {f})`
        return if (cl.reach == CleanReach.AT_AND_BELOW) listOf(kept)
               else listOf(kept, c.copy(fact = c.fact.copy(path = p, tail = Tail.EXACT), exclusion = ExclusionSet.Empty))   // + x.p.f.$
    }
    return listOf(
        if ((c.fact.tail.isAny || c.fact.tail == Tail.STAR) && cl.reach == CleanReach.BELOW && q == p)
            c.copy(fact = c.fact.copy(tail = Tail.EXACT), exclusion = ExclusionSet.Empty)   // in the layer of c
        else c.copy(demand = true))
}

sealed interface CheckResult { data object None : CheckResult; data object Holds : CheckResult; data class Request(val mark: TaintMark) : CheckResult }

/** ap.md §4.9 and §4.6 (Lean `check`, `ND.DN.conj`; renamed: `check` is the Kotlin assert): the check of one mark literal `s`
 *  on one fact. The tree form is ApOps.checkMark (Part I §5.8). The §11.2 difference: the effective-mark case is asserted away. */
fun markCheck(i: Pattern, f: Conclusion, s: Pattern, restricted: Boolean = false): CheckResult {
    val t = (s.fact.mark as MarkSlot.Concrete).mark
    if (!overlap(Pattern(f.fact, f.exclusion), s)) return CheckResult.None
    return when (val mk = f.fact.mark) {
        is MarkSlot.Concrete -> if (mk.mark == t) CheckResult.Holds else CheckResult.None
        is MarkSlot.Star -> if (restricted || t in mk.excluded) CheckResult.None
                            else { check(i.fact.mark is MarkSlot.Star); CheckResult.Request(t) }
    }
}

/** ap.md §4.6 (Lean ND.conjLayer; with the `[any-taint]` rule AnyTaintND.conjLayerT): the layer of one input of a literal
 *  that holds on it. Demand if the input is in the demand layer, or if the literal does not cover it and it is not
 *  `[any-taint]` (a normal `[any-taint]` input that overlaps its literal and passes its mark gate keeps the result
 *  normal: every location of it carries the mark, AnyTaintND.lit_loc). The overlap of `markCheck` reads the exclusion of
 *  an `[any-taint]/E` input (A2), so an input in the excluded part never reaches here.
 *  For the legal matched TAINT literal shapes, CurrentProposal.LiteralLayer proves this equals f.demand. */
fun conjDemand(f: Conclusion, lit: Pattern): Boolean =
    f.demand || (!covers(lit, Pattern(f.fact, f.exclusion)) && f.fact.tail != Tail.ANY_TAINT)

/** ap.md §4.5 chain answer (Lean answerInit) and §4.10 item 4 (Lean Statics.SCtx.ansInit). Precondition: a overlaps i, a.mark = t.
 *  Run 1 has no must-premise (W8 (c)): an `[any-taint]/E` `a` gives the static mark answer with the tail `[any]` and no
 *  exclusion (a larger premise, demand: sound). */
fun answer(i: Pattern, a: Pattern, t: TaintMark): Pattern = when {
    i.fact.base == STATIC && a.fact.path.startsWith(i.fact.path) ->          // a at or below a static premise: a itself
        if (a.fact.tail == Tail.ANY_TAINT) Pattern(a.fact.copy(mark = MarkSlot.Concrete(t), tail = Tail.ANY), ExclusionSet.Empty)   // `[any]`: no E
        else Pattern(a.fact.copy(mark = MarkSlot.Concrete(t)), a.exclusion)
    a.fact.tail == Tail.EXACT && a.fact.path == i.fact.path ->
        Pattern(PathFact(i.fact.base, i.fact.path, Tail.EXACT, MarkSlot.Concrete(t)), ExclusionSet.Empty)
    else -> Pattern(i.fact.copy(mark = MarkSlot.Concrete(t)), i.exclusion)   // the request chain and kind, mark t
}

/** ap.md §6.2 (Lean policy1). */
fun policy(a: Pattern): Pattern =
    if (a.fact.base == AccessPathBase.Zero) a
    else Pattern(PathFact(a.fact.base, emptyList(), Tail.STAR, MarkSlot.STAR), ExclusionSet.Empty)

/** Generic micro-edge reversal (Lean revEdge, revKinds, MarkRev), unchanged by record read views.
 *  It rejects a must premise and a must conclusion with nonempty exclusion; reverseRecordLeaf handles the supported
 *  native forward must shapes separately (§7.8). A forward must micro target still reverses to ordinary ANY.
 *  MicroEdge.may reads the forward target for pass-rule demand handling. */
fun revEdge(e: PathEdge): PathEdge? {
    if (e.from.tail == Tail.ANY_TAINT) return null                          // generic reversal only
    if (e.to.tail == Tail.ANY_TAINT && (e.toExclusion != ExclusionSet.Empty || e.exclusion != ExclusionSet.Empty))
        return null                                                         // generic reversal only
    val fAbstract = e.to.mark is MarkSlot.Star
    if (!fAbstract && e.from.mark !is MarkSlot.Concrete) return null       // no_rev_of_star_conc
    val (pt, ct) = revTails(e.from.tail, e.to.tail)
    val pm = if (fAbstract) e.from.mark else e.to.mark                     // the new premise never has `*∖X`
    val cm = if (fAbstract) e.to.mark else e.from.mark
    val excl = if (pt == Tail.STAR || ct == Tail.STAR) e.exclusion else ExclusionSet.Empty   // the exclusion goes to the new conclusion (W1)
    return PathEdge(PathFact(e.to.base, e.to.path, pt, pm), PathFact(e.from.base, e.from.path, ct, cm), excl)
}

fun revTails(i: Tail, f: Tail): Pair<Tail, Tail> = when (i) {             // the table of §9.1
    Tail.STAR -> when (f) {
        Tail.STAR -> Tail.STAR to Tail.STAR; Tail.EXACT -> Tail.EXACT to Tail.ANY; Tail.ANY -> Tail.ANY to Tail.ANY
        Tail.ANY_TAINT -> error("S15: a taint edge has an EXACT or ANY premise; a `*` premise has no `[any-taint]` conclusion")
    }
    Tail.ANY -> when (f) {
        Tail.STAR -> Tail.STAR to Tail.STAR; Tail.EXACT -> Tail.EXACT to Tail.ANY; Tail.ANY -> Tail.ANY to Tail.ANY
        Tail.ANY_TAINT -> Tail.ANY to Tail.ANY                               // a conditional source with an `[any]` literal (A1)
    }
    Tail.EXACT -> when (f) {
        Tail.STAR -> Tail.EXACT to Tail.EXACT; Tail.EXACT -> Tail.EXACT to Tail.EXACT; Tail.ANY -> Tail.ANY to Tail.EXACT
        Tail.ANY_TAINT -> Tail.ANY to Tail.EXACT                              // a source result: the premise `[any]` (A1)
    }
    Tail.ANY_TAINT -> error("generic revTails has no must-premise row")   // reverseRecordLeaf handles native must views
}

/** ap.md §8.1 (Subsume.subsumesB, markSubsB): s subsumes n inside one layer. FlowGroup and TaintGroup are its tree form.
 *  An `[any]` s (demand) subsumes every fact at or below its path with its mark. An `[any-taint]/Es` s (normal)
 *  subsumes, with its mark, in its layer, ONLY `[any-taint]` facts: an `[any-taint]/En` fact at its path if `Es ⊆ En`,
 *  and one strictly below its path through an accessor that `Es` admits (A2; argued, ap.md §11.2); NEVER a `$` fact
 *  (DD16, ap-history.md F69: a later demoting cleaner row moves s to the demand layer, and the `$` fact stays normal). */
fun subsumes(s: Conclusion, n: Conclusion): Boolean {
    if (s.fact.base != n.fact.base || s.demand != n.demand || !markSubsumes(s.fact.mark, n.fact.mark)) return false
    return when (s.fact.tail) {
        Tail.ANY -> n.fact.path.startsWith(s.fact.path)
        Tail.ANY_TAINT -> n.fact.tail == Tail.ANY_TAINT && n.fact.path.startsWith(s.fact.path) &&
            if (n.fact.path.size == s.fact.path.size) s.exclusion.isSubsetOf(n.exclusion)
            else s.exclusion.admits(n.fact.path[s.fact.path.size])
        Tail.STAR -> n.fact.tail == Tail.STAR && s.fact.path == n.fact.path && s.exclusion.isSubsetOf(n.exclusion)
        Tail.EXACT -> n.fact.tail == Tail.EXACT && s.fact.path == n.fact.path
    }
}
fun markSubsumes(s: MarkSlot, n: MarkSlot): Boolean = when (s) {
    is MarkSlot.Concrete -> n == s
    is MarkSlot.Star -> n is MarkSlot.Star && s.excluded.isSubsetOf(n.excluded)
}

/** R1 publishes normal singleton summaries except backward zero summaries. */
fun r1Eligible(premise: PremiseKey, g: Conclusion, direction: Direction): Boolean =
    !g.demand && premise is InitialAp && !(direction == Direction.BACKWARD && premise.isZero)

/** F77 selects demand edges by structure, before any transient read-view conversion. */
fun demandSelected(premise: PremiseKey, g: Conclusion, direction: Direction): Boolean =
    g.demand || premise.size > 1 || (direction == Direction.BACKWARD && premise.isZero)
