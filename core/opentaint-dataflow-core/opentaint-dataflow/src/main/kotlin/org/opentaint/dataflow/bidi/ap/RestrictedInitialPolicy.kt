package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor

internal data class RawInitialCommand(val emission: InitialEmission, val possible: Boolean = false)

/** One run's pure C2 policy. Image tests inspect templates; they never intern hypothetical facts. */
class RestrictedInitialPolicy(
    val run: Int = 2,
    val fieldLimit: Int = Int.MAX_VALUE,
    val direction: Direction = if (run % 2 == 0) Direction.BACKWARD else Direction.FORWARD,
    private val catalog: MarkTable? = null,
    val revised: Boolean = false,
) {
    init { require(run >= 2 && fieldLimit >= 1) }

    fun emit(demand: Pattern, actual: Pattern): Pattern? {
        if (revised) return rawCommands(demand, actual, intrinsicInitialLayer(actual)).firstOrNull()?.emission?.pattern
        if (!validDemand(demand) || actual.fact.tail == Tail.NON_EMPTY_MAY) return null
        val d = normalizeDemandFieldExclusion(demand)
        if (d.fact.base != actual.fact.base || !markSub(d.fact.mark, actual.fact.mark, catalog)) return null
        if (d.fact.base == AccessPathBase.Zero && !canonicalZero(actual)) return null
        if (!fitsBudget(d) || !fitsBudget(actual)) return null
        // Only a concrete MAY witness can supply a provisional exact data point.
        if (d.fact.tail == Tail.EXACT && actual.fact.tail == Tail.ANY && d.fact.mark is MarkSlot.Star) return null
        val p = d.fact.path
        val q = actual.fact.path
        val mark = boundMark(d.fact.mark, actual.fact.mark)
        fun result(path: List<Int>, tail: Tail, e: ExclusionSet = ExclusionSet.Empty): Pattern? {
            val value = Pattern(PathFact(d.fact.base, path, tail, mark), e)
            return value.takeIf(::legalInitial)
        }
        if (q == p) return when (d.fact.tail) {
            Tail.ANY -> when (actual.fact.tail) {
                Tail.STAR -> result(p, Tail.STAR)
                Tail.EXACT -> result(p, Tail.EXACT)
                Tail.ANY -> result(p, Tail.STAR)
                Tail.ANY_TAINT -> result(p, Tail.ANY_TAINT, actual.exclusion)
                Tail.NON_EMPTY_MAY -> null
            }
            Tail.STAR, Tail.EXACT -> result(p, Tail.EXACT)
            Tail.ANY_TAINT, Tail.NON_EMPTY_MAY -> null // Only legacy entries reach this lane.
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
        if (p.startsWith(q) && actual.fact.tail in setOf(Tail.ANY, Tail.ANY_TAINT) &&
            actual.tailAdmits(p.drop(q.size))) return when (d.fact.tail) {
            Tail.ANY -> when (actual.fact.tail) {
                Tail.ANY -> result(p, Tail.STAR)
                Tail.ANY_TAINT -> result(p, Tail.ANY_TAINT, d.exclusion)
                else -> null
            }
            Tail.STAR, Tail.EXACT -> result(p, Tail.EXACT)
            Tail.ANY_TAINT, Tail.NON_EMPTY_MAY -> null
        }
        return null
    }

    /** The scalar primary is kept for reference checks. Production uses the complete family. */
    fun emitAdmission(demand: Pattern, actual: Pattern, actualLayer: Layer): InitialEmission? {
        if (revised) return rawCommands(demand, actual, actualLayer).firstOrNull()?.emission
        val emitted = emit(demand, actual) ?: return null
        return InitialEmission(emitted, admissionLayer(emitted, actual, actualLayer))
    }

    /** Every admitted start is an identity. Companions require a successful primary. */
    fun emitAdmissions(demand: Pattern, actual: Pattern, actualLayer: Layer): List<InitialEmission> {
        if (revised) return rawCommands(demand, actual, actualLayer).map { it.emission }
        val primary = emitAdmission(demand, actual, actualLayer) ?: return emptyList()
        val result = linkedSetOf(primary)
        val shape = primary.pattern
        if (shape.fact.tail == Tail.STAR && shape.fact.mark is MarkSlot.Concrete) {
            result += InitialEmission(shape.copy(fact = shape.fact.copy(mark = MarkSlot.STAR)), Layer.NORMAL)
        }
        if (demand.fact.tail == Tail.ANY && actual.fact.path.size > demand.fact.path.size &&
            actual.fact.path.startsWith(demand.fact.path)) {
            result += InitialEmission(Pattern(PathFact(demand.fact.base, demand.fact.path, Tail.EXACT,
                MarkSlot.STAR), ExclusionSet.Empty), Layer.NORMAL)
        }
        check(result.none { it.pattern.fact.tail == Tail.ANY })
        return result.toList()
    }

    /** Complete structural output image, including the non-idempotent run-2 requested STAR. */
    fun canEmitInitial(demand: Pattern, initial: Pattern): Boolean {
        if (revised) return rawWitness(demand, initial) != null
        if (!validDemand(demand)) return false
        val d = normalizeDemandFieldExclusion(demand)
        if (!legalInitial(initial) || !fitsBudget(d) || d.fact.base != initial.fact.base ||
            !renderedMark(d.fact.mark, initial.fact.mark)) return false
        val p = d.fact.path
        val q = initial.fact.path
        if (q == p) return when (initial.fact.tail) {
            Tail.EXACT -> initial.exclusion == ExclusionSet.Empty && d.fact.tail != Tail.ANY_TAINT
            Tail.ANY, Tail.NON_EMPTY_MAY -> false
            Tail.ANY_TAINT -> d.fact.tail == Tail.ANY
            Tail.STAR -> initial.exclusion == ExclusionSet.Empty && d.fact.tail == Tail.ANY ||
                run == 2 && d.fact.tail == Tail.STAR && initial.exclusion == d.exclusion &&
                p.count { it.isCounted() } < fieldLimit &&
                !(initial.fact.base == STATIC && p.size == 1)
        }
        if (d.fact.tail != Tail.ANY || !q.startsWith(p) || !d.tailAdmits(q.drop(p.size))) return false
        val end = firstFieldEnd(d.fact.base, p, q) ?: return false
        return end == q.size && initial.exclusion == ExclusionSet.Empty &&
            (initial.fact.tail == Tail.STAR || initial.fact.tail == Tail.EXACT && initial.fact.mark is MarkSlot.Concrete)
    }

    /** Public C5 keys use the complete normalized C2 image, without interning query witnesses. */
    fun canStoreInitial(entry: Pattern, stored: Pattern): Boolean {
        if (revised) return rawWitness(entry, stored) != null
        fun primaryImage(candidate: Pattern): Boolean {
            fun fits(raw: Pattern): Boolean = canEmitInitial(entry, raw) && insideDemand(raw, entry, catalog)
            if (fits(candidate)) return true
            return candidate.fact.mark is MarkSlot.Star && candidate.fact.tail == Tail.STAR &&
                candidate.exclusion == ExclusionSet.Empty &&
                fits(candidate.copy(fact = candidate.fact.copy(tail = Tail.EXACT)))
        }
        if (!validDemand(entry)) return false
        if (primaryImage(stored)) return true
        if (stored.fact.mark !is MarkSlot.Star || !stored.fact.mark.excluded.isEmpty ||
            stored.fact.tail != Tail.STAR || entry.fact.mark !is MarkSlot.Concrete) return false
        // A concrete STAR primary authorizes exactly its FLOW companion. This does not synthesize T.
        return primaryImage(stored.copy(fact = stored.fact.copy(mark = entry.fact.mark)))
    }

    internal fun rawCommands(demand: Pattern, actual: Pattern, layer: Layer): List<RawInitialCommand> {
        if (!validDemand(demand) || !legalActual(actual, layer)) return emptyList()
        val d = normalizeDemandFieldExclusion(demand)
        val p = d.fact.path
        val q = actual.fact.path
        if (d.fact.base != actual.fact.base || !markSub(d.fact.mark, actual.fact.mark, catalog) ||
            !fitsBudget(d) || !legalPath(d) || d.fact.tail == Tail.ANY_TAINT ||
            d.fact.tail == Tail.EXACT && d.fact.mark is MarkSlot.Star) return emptyList()
        val mark = if (d.fact.mark is MarkSlot.Star) MarkSlot.STAR else boundMark(d.fact.mark, actual.fact.mark)
        val commands = LinkedHashSet<RawInitialCommand>()
        val cap = relativeCap(d)
        val relay = run == 2 && direction == Direction.BACKWARD
        fun add(path: List<Int>, tail: Tail, e: ExclusionSet = ExclusionSet.Empty,
                possible: Boolean = false, supported: Boolean = true) {
            val conclusionLayer = if (mark is MarkSlot.Star) Layer.NORMAL else
                Layer.NORMAL or (tail == Tail.STAR || layer == Layer.DEMAND || !supported)
            val revisedHead = tail == Tail.STAR && e == ExclusionSet.Empty &&
                d.fact.tail.isMay && mark is MarkSlot.Concrete &&
                direction == Direction.FORWARD && layer == Layer.NORMAL &&
                actual.fact.tail == Tail.ANY_TAINT && actual.exclusion != ExclusionSet.Empty &&
                q.size > path.size && q.startsWith(path)
            val revisedMask = tail == Tail.STAR && e == ExclusionSet.Empty &&
                mark is MarkSlot.Concrete && q == path &&
                (actual.fact.tail == Tail.STAR || actual.fact.tail == Tail.ANY_TAINT)
            val key = Pattern(PathFact(d.fact.base, if (revisedHead) q else path, tail, mark),
                if (revisedHead || revisedMask) actual.exclusion else e)
            if (!legalInitial(key) || !revisedHead && depth(key) > cap) return
            commands += RawInitialCommand(InitialEmission(key, conclusionLayer), possible)
            if (tail == Tail.STAR && mark is MarkSlot.Concrete) {
                val flow = key.copy(fact = key.fact.copy(mark = MarkSlot.STAR))
                commands += RawInitialCommand(InitialEmission(flow, Layer.NORMAL), possible)
            }
        }
        fun atHead(tail: Tail, e: ExclusionSet, possible: Boolean) {
            val definite = !possible && (tail == Tail.EXACT || tail == Tail.ANY_TAINT)
            when (d.fact.tail) {
                Tail.EXACT, Tail.STAR -> when {
                    tail == Tail.NON_EMPTY_MAY -> Unit
                    tail == Tail.STAR -> if (d.fact.tail == Tail.STAR && relay)
                        add(p, Tail.STAR, d.exclusion)
                    else -> add(p, Tail.EXACT, possible = possible, supported = definite)
                }
                Tail.ANY, Tail.NON_EMPTY_MAY -> when (tail) {
                    Tail.EXACT -> if (d.fact.tail == Tail.ANY) add(p, Tail.EXACT, possible = possible, supported = definite)
                    Tail.STAR, Tail.NON_EMPTY_MAY -> add(p, Tail.STAR, possible = possible)
                    Tail.ANY -> {
                        if (d.fact.tail == Tail.ANY) add(p, Tail.EXACT, possible = possible, supported = false)
                        add(p, Tail.STAR, possible = possible)
                    }
                    Tail.ANY_TAINT -> add(p, Tail.ANY_TAINT, e, possible = possible, supported = definite)
                }
                Tail.ANY_TAINT -> Unit
            }
        }
        when {
            q == p -> atHead(actual.fact.tail, actual.exclusion, possible = false)
            q.startsWith(p) && d.tailAdmits(q.drop(p.size)) -> when (d.fact.tail) {
                Tail.STAR -> if (relay) add(p, Tail.STAR, d.exclusion)
                Tail.ANY, Tail.NON_EMPTY_MAY -> {
                    val end = firstFieldEnd(d.fact.base, p, q) ?: return emptyList()
                    val head = q.take(end)
                    if (end < q.size || actual.fact.tail !in setOf(Tail.EXACT, Tail.ANY)) add(head, Tail.STAR)
                    else {
                        add(head, Tail.EXACT, supported = actual.fact.tail == Tail.EXACT)
                        if (actual.fact.tail == Tail.ANY) add(head, Tail.STAR)
                    }
                    if (d.fact.tail == Tail.ANY && commands.isNotEmpty()) {
                        val probe = Pattern(PathFact(d.fact.base, p, Tail.EXACT, MarkSlot.STAR), ExclusionSet.Empty)
                        if (legalInitial(probe)) commands += RawInitialCommand(InitialEmission(probe, Layer.NORMAL))
                    }
                }
                else -> Unit
            }
            p.startsWith(q) && actual.tailAdmits(p.drop(q.size)) -> when (actual.fact.tail) {
                Tail.ANY, Tail.NON_EMPTY_MAY -> atHead(Tail.ANY, ExclusionSet.Empty, possible = false)
                Tail.ANY_TAINT -> atHead(Tail.ANY_TAINT, ExclusionSet.Empty, possible = false)
                Tail.STAR -> if (d.fact.tail.isMay) atHead(Tail.ANY, ExclusionSet.Empty, possible = true)
                Tail.EXACT -> Unit
            }
        }
        return commands.toList()
    }

    /** Query children are selected by the owner's frozen view. Use the parent's cap. */
    internal fun preparedChild(demand: Pattern, actual: Pattern, layer: Layer, child: List<Int>): List<RawInitialCommand> {
        val d = normalizeDemandFieldExclusion(demand)
        if (!d.fact.tail.isMay || !child.startsWith(d.fact.path) ||
            firstFieldEnd(d.fact.base, d.fact.path, child) != child.size) return emptyList()
        if (!d.tailAdmits(child.drop(d.fact.path.size))) return emptyList()
        val q = actual.fact.path
        val possible = child.size > q.size && child.startsWith(q) && actual.fact.tail != Tail.ANY_TAINT
        val tails = when {
            q == child -> when (actual.fact.tail) {
                Tail.EXACT -> listOf(Tail.EXACT)
                Tail.ANY, Tail.ANY_TAINT -> listOf(Tail.EXACT, Tail.STAR)
                else -> listOf(Tail.STAR)
            }
            q.startsWith(child) -> listOf(Tail.STAR)
            child.startsWith(q) && actual.tailAdmits(child.drop(q.size)) -> listOf(Tail.EXACT, Tail.STAR)
            else -> return emptyList()
        }
        val mark = if (d.fact.mark is MarkSlot.Star) MarkSlot.STAR else boundMark(d.fact.mark, actual.fact.mark)
        val result = ArrayList<RawInitialCommand>(3)
        for (tail in tails) {
            val mask = if (child == q && tail == Tail.STAR && mark is MarkSlot.Concrete &&
                (actual.fact.tail == Tail.STAR || actual.fact.tail == Tail.ANY_TAINT)) actual.exclusion else ExclusionSet.Empty
            val key = Pattern(PathFact(d.fact.base, child, tail, mark), mask)
            if (!legalInitial(key) || depth(key) > relativeCap(d)) continue
            val demandLayer = mark is MarkSlot.Concrete && (tail == Tail.STAR || layer == Layer.DEMAND ||
                possible || actual.fact.tail.isMay)
            result += RawInitialCommand(InitialEmission(key, Layer.NORMAL or demandLayer), possible)
            if (tail == Tail.STAR && mark is MarkSlot.Concrete)
                result += RawInitialCommand(InitialEmission(key.copy(fact = key.fact.copy(mark = MarkSlot.STAR)), Layer.NORMAL), possible)
        }
        return result
    }

    /** Witness paths are the requested head, the selector head and the one-field
     * extension needed by a concrete MAY selector's conditional exact FLOW probe. */
    internal fun rawWitness(entry: Pattern, key: Pattern): Pair<Pattern, Layer>? {
        if (!legalInitial(key) || key.fact.base != entry.fact.base) return null
        if (key.fact.base == AccessPathBase.Zero) return if (canonicalZero(entry)) key to Layer.NORMAL else null
        val star = key.fact.mark as? MarkSlot.Star
        val target = entry.fact.mark as? MarkSlot.Concrete
        val mark = if (target == null) key.fact.mark else if (star == null) key.fact.mark else target
        if (!markSub(entry.fact.mark, mark, catalog)) return null
        val p = entry.fact.path
        val q = key.fact.path
        val paths = linkedSetOf(q)
        if (p == q && entry.fact.tail == Tail.ANY && target != null && star != null && key.fact.tail == Tail.EXACT &&
            depth(entry) < fieldLimit) {
            if (key.fact.base != STATIC || p.size >= 2) paths += (p + ELEMENT_ACCESSOR_IDX)
        }
        for (path in paths) for (tail in Tail.entries) {
            val e = if (path == q && tail in setOf(Tail.STAR, Tail.ANY_TAINT)) key.exclusion else ExclusionSet.Empty
            val mx = if (mark is MarkSlot.Star && entry.fact.mark is MarkSlot.Star) entry.fact.mark else mark
            val offer = Pattern(PathFact(key.fact.base, path, tail, mx), e)
            val layer = if (tail.isMay || tail == Tail.STAR && mark is MarkSlot.Concrete) Layer.DEMAND else Layer.NORMAL
            if (rawCommands(entry, offer, layer).any { it.emission.pattern == key }) return offer to layer
        }
        return null
    }

    /** A raw query can have an uncertain binding only at a named M/NE head
     * or at the single counted child allowed by a prepared parent. */
    internal fun needsPossibleQualification(entry: Pattern, key: InitialAp): Boolean {
        if (!entry.fact.tail.isMay || key.exclusion != ExclusionSet.Empty ||
            key.tail != Tail.EXACT && key.tail != Tail.STAR) return false
        val p = entry.fact.path
        val q = key.pathData.asList()
        return if (p == q) p.isNotEmpty() else q.startsWith(p) && firstFieldEnd(key.base, p, q) == q.size
    }

    private fun legalActual(p: Pattern, layer: Layer): Boolean {
        if (!fitsBudget(p) || p.fact.tail == Tail.ANY_TAINT && direction != Direction.FORWARD) return false
        if (p.fact.base == AccessPathBase.Zero) return canonicalZero(p)
        if (p.fact.tail.isMay && (p.exclusion != ExclusionSet.Empty || layer != Layer.DEMAND)) return false
        if (p.fact.tail == Tail.EXACT && p.fact.mark is MarkSlot.Concrete &&
            p.exclusion != ExclusionSet.Empty) return false
        if (p.fact.mark is MarkSlot.Concrete &&
            (p.fact.mark.mark == TaintMark.ZERO || catalog?.isGroup(p.fact.mark.mark) == true)) return false
        return legalPath(p)
    }

    private fun depth(p: Pattern): Int = p.fact.path.count { it.isCounted() }

    private fun relativeCap(d: Pattern): Int {
        val depth = depth(d)
        return if (depth >= fieldLimit) fieldLimit else depth + 1
    }

    private fun boundMark(required: MarkSlot, actual: MarkSlot): MarkSlot =
        if (required is MarkSlot.Concrete && catalog?.isGroup(required.mark) == true &&
            actual is MarkSlot.Concrete) actual else required

    private fun renderedMark(required: MarkSlot, rendered: MarkSlot): Boolean =
        if (required is MarkSlot.Star) rendered == required
        else rendered is MarkSlot.Concrete && markSub(required, rendered, catalog)

    private fun fitsBudget(p: Pattern): Boolean = p.fact.path.count { it.isCounted() } <= fieldLimit

    private fun validDemand(p: Pattern): Boolean =
        (revised || p.fact.tail != Tail.NON_EMPTY_MAY) &&
            !(p.fact.tail == Tail.EXACT && p.fact.mark is MarkSlot.Concrete && p.exclusion != ExclusionSet.Empty) &&
            (p.fact.base != AccessPathBase.Zero || canonicalZero(p))

    private fun canonicalZero(p: Pattern): Boolean = p.fact.path.isEmpty() && p.fact.tail == Tail.EXACT &&
        p.exclusion == ExclusionSet.Empty && p.fact.mark == MarkSlot.Concrete(TaintMark.ZERO)

    private fun legalInitial(p: Pattern): Boolean {
        if (!fitsBudget(p) || p.fact.tail.isMay || p.fact.tail == Tail.ANY_TAINT && direction == Direction.BACKWARD) return false
        if (p.fact.mark is MarkSlot.Concrete && catalog?.isGroup(p.fact.mark.mark) == true) return false
        if (p.fact.tail != Tail.STAR && p.fact.tail != Tail.ANY_TAINT && p.exclusion != ExclusionSet.Empty) return false
        if (p.fact.mark is MarkSlot.Star && !p.fact.mark.excluded.isEmpty) return false
        if (p.fact.base == AccessPathBase.Zero) return p.fact.path.isEmpty() && p.fact.tail == Tail.EXACT &&
            p.exclusion == ExclusionSet.Empty && p.fact.mark == MarkSlot.Concrete(TaintMark.ZERO)
        if (revised) return legalPath(p)
        if (p.fact.base != STATIC || p.fact.mark is MarkSlot.Star) return true
        val path = p.fact.path
        return path.size == 1 && path[0].isClass() && p.fact.tail == Tail.EXACT ||
            path.size >= 2 && path[0].isClass() && path[1].isFieldAccessor()
    }

    private fun legalPath(p: Pattern): Boolean {
        val path = p.fact.path
        if (p.fact.base != STATIC) return path.all { it.isCounted() }
        if (path.isEmpty()) return p.fact.mark is MarkSlot.Star
        if (!path[0].isClass()) return false
        if (p.fact.mark is MarkSlot.Star) return path.size == 1 ||
            path[1].isFieldAccessor() && path.drop(2).all { it.isCounted() }
        return path.size == 1 && path[0].isClass() && p.fact.tail == Tail.EXACT ||
            path.size >= 2 && path[1].isFieldAccessor() && path.drop(2).all { it.isCounted() }
    }

    /** A JVM static anchor is indivisible. A raw array element cannot become a class abstraction. */
    private fun firstFieldEnd(base: AccessPathBase, prefix: List<Int>, path: List<Int>): Int? {
        val index = (prefix.size until path.size).firstOrNull { path[it].isCounted() } ?: return null
        val end = index + 1
        if (base == STATIC && (end < 2 || !path[0].isClass() || !path[1].isFieldAccessor())) return null
        return end
    }
}
