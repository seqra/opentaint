package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx

internal fun ApManager.compile(e: PathEdge): CompiledEdge = CompiledEdge(
    e.from.base, e.from.path.toIntArray(), e.from.tail, e.from.mark,
    e.to.base, path(e.to.path), e.to.tail, e.to.mark,
    intern(e.exclusion), intern(e.fromExclusion), intern(e.toExclusion))

/** Immutable edge form. The from-path array belongs to this value. */
internal class CompiledEdge(
    val fromBase: AccessPathBase, fromPath: IntArray, val fromTail: Tail, val fromMark: MarkSlot,
    val toBase: AccessPathBase, val toPath: PathNode?, val toTail: Tail, val toMark: MarkSlot,
    val exclusion: ExclusionSet,
    val fromExclusion: ExclusionSet = ExclusionSet.Empty,
    val toExclusion: ExclusionSet = ExclusionSet.Empty,
) {
    internal val fromPathData = fromPath.copyOf()
    val fromPath: IntArray get() = fromPathData.copyOf()

    init {
        check(fromMark !is MarkSlot.Star || fromMark.excluded.isEmpty) { "S7: a premise cannot exclude marks" }
        check(toMark !is MarkSlot.Concrete || fromMark is MarkSlot.Concrete) { "S7: a concrete target needs a concrete premise" }
        check(fromTail != Tail.EXACT || toTail != Tail.STAR || fromMark is MarkSlot.Star) {
            "A concrete exact premise cannot have a STAR target"
        }
        check(toTail != Tail.ANY_TAINT || toMark is MarkSlot.Concrete || fromMark is MarkSlot.Star) {
            "An abstract must target needs a FLOW relation"
        }
        check(fromTail == Tail.STAR || toTail == Tail.STAR || exclusion == ExclusionSet.Empty) { "W1: only STAR sides have shared E" }
        check(fromTail == Tail.ANY_TAINT || fromExclusion == ExclusionSet.Empty) { "A2: only a must premise has own E" }
        check(toTail == Tail.ANY_TAINT || toExclusion == ExclusionSet.Empty) { "A2: only a must target has own E" }
    }
}

/** The tree form of concat. Field cuts belong to the caller. */
internal class EdgeApplication(private val m: ApManager, private val ce: CompiledEdge,
                               private val edgeDemand: Boolean, private val mode: ApMode,
                               private val out: ApOut, private val unchangedStaticInitial: InitialAp? = null) {
    val results = Results(m, ce.toBase)
    private val gate = MarkGate(m, ce.fromMark, ce.toMark, mode)
    private val admitsRest = { a: AccessorIdx ->
        val premiseAdmits = when (ce.fromTail) {
            Tail.EXACT -> false
            Tail.ANY_TAINT -> ce.fromExclusion.admits(a)
            else -> ce.exclusion.admits(a)
        }
        premiseAdmits && (ce.toTail != Tail.STAR || ce.exclusion.admits(a))
    }
    private val aboveTail = if (ce.toTail == Tail.EXACT) Tail.EXACT else Tail.ANY
    private val mustAboveTail = when (ce.toTail) {
        Tail.EXACT -> Tail.EXACT
        Tail.ANY -> Tail.ANY
        Tail.STAR, Tail.ANY_TAINT -> Tail.ANY_TAINT
    }
    private val aboveExclusion = if (ce.toTail == Tail.ANY_TAINT) ce.toExclusion else ce.exclusion
    private var requested = false

    fun reach(c: Reach) {
        check(ce.fromPathData.isEmpty() && !ce.fromTail.isAny)
        gate.taintMarks(m.markSetOf(TaintMark.ZERO))?.let { put(c.layer or edgeDemand, ce.toTail, it, ce.toExclusion) }
    }

    fun flow(c: FlowTree, staticAt: Int) {
        // F78: exclusion creation also creates interest on the original abstract
        // slot. Do this before the positional/mark tests and before any output.
        // The engine's collector applies the normal-origin and static-root guards.
        if (mode.run1) (ce.toMark as? MarkSlot.Star)?.excluded?.data?.forEach { id ->
            m.cancellation.checkpoint()
            out.markRequest(m.marks.runtimeAtom(TaintMark(id), mode.markMode))
            if ((ce.fromMark as? MarkSlot.Concrete)?.mark?.id == id) requested = true
        }
        val mx = gate.flowMarks(c.markExclusion)
        val exact = c.tail == Tail.EXACT
        val must = c.tail == Tail.ANY_TAINT
        val normal = c.tail != Tail.ANY
        val writeKeep = ce.fromBase == ce.toBase && ce.fromTail == Tail.STAR &&
            ce.toTail == Tail.STAR && ce.fromPathData.contentEquals(ce.toPath?.toIntArray() ?: EMPTY_PATH) &&
            ce.exclusion != ExclusionSet.Empty
        val layer = c.layer or edgeDemand
        val unchanged = if (mode.run1 && mode.markMode == MarkMode.FULL) unchangedStaticFlowPath(c, unchangedStaticInitial) else null
        val u = c.root.walk(ce.fromPathData) { d, n ->
            m.cancellation.checkpoint()
            if (n.leaf.isEmpty || (normal && !c.exclusion.admits(ce.fromPathData[d]))) return@walk
            if (normal && d == staticAt) {
                // Prescan catalog emission replaces the old position request. This parent gives no fact.
            } else if (!exact || writeKeep) flowHit(mx, c, { !sameFlowLeaf(m, unchanged, ce.fromPathData, d) }) {
                if (must) {
                    val tail = if (layer == Layer.DEMAND) Tail.ANY else mustAboveTail
                    results.flow(if (tail == Tail.ANY) Layer.DEMAND else layer,
                        if (tail == Tail.ANY || tail == Tail.EXACT) ExclusionSet.Empty else aboveExclusion, it, flagAtTarget(), tail)
                } else results.flow(Layer.DEMAND, ExclusionSet.Empty, it, flagAtTarget())
            }
        } ?: return
        val kids = FlowAlgebra.retainChildren(u, m.cancellation, admitsRest)
        when (ce.toTail) {
            Tail.STAR -> {
                if (kids != null) flowHit(mx, c, { changedFlowSubtree(m, kids, ce.fromPathData, unchanged) }) {
                    if (layer == Layer.DEMAND && (exact || must))
                        results.flow(Layer.DEMAND, ExclusionSet.Empty, it, FlowAlgebra.prepend(m, ce.toPath, kids), Tail.ANY)
                    else results.flow(layer, c.exclusion, it, FlowAlgebra.prepend(m, ce.toPath, kids), c.tail)
                }
                if (!u.leaf.isEmpty) flowHit(mx, c, {
                    !sameFlowLeaf(m, unchanged, ce.fromPathData, ce.fromPathData.size)
                }) {
                    if (mode.run1 && ce.exclusion != ExclusionSet.Empty && c.tail != Tail.ANY)
                        results.flow(Layer.DEMAND, ExclusionSet.Empty, it, flagAtTarget(), c.tail)
                    else if (layer == Layer.DEMAND && (exact || must))
                        results.flow(Layer.DEMAND, ExclusionSet.Empty, it, flagAtTarget(), Tail.ANY)
                    else results.flow(layer, c.exclusion.union(ce.exclusion), it, flagAtTarget(), c.tail)
                }
            }
            else -> if (kids != null || !u.leaf.isEmpty) flowHit(mx, c, {
                (!u.leaf.isEmpty && !sameFlowLeaf(m, unchanged, ce.fromPathData, ce.fromPathData.size)) ||
                    (kids != null && changedFlowSubtree(m, kids, ce.fromPathData, unchanged))
            }) {
                val tail = if (layer == Layer.DEMAND && ce.toTail != Tail.ANY) Tail.ANY else ce.toTail
                val exclusion = when (tail) {
                    Tail.ANY_TAINT -> ce.toExclusion
                    Tail.EXACT -> ExclusionSet.Empty
                    else -> ExclusionSet.Empty
                }
                results.flow(if (tail == Tail.ANY) Layer.DEMAND else layer, exclusion, it, flagAtTarget(), tail)
            }
        }
    }

    private inline fun flowHit(mx: MarkExclusions?, c: FlowTree, changed: () -> Boolean, add: (MarkExclusions) -> Unit) {
        if (mx != null) { add(mx); return }
        val mark = gate.flowRequest(c.markExclusion) ?: return
        if (mode.run1 && !requested && changed()) { out.markRequest(mark); requested = true }
    }

    fun taint(c: TaintTree) {
        val layer = c.layer or edgeDemand
        val must = c.anyTail == Tail.ANY_TAINT
        val e = c.exclusion
        val u = c.root.walk(ce.fromPathData) { d, n ->
            m.cancellation.checkpoint()
            if (!e.admits(ce.fromPathData[d])) return@walk
            gate.taintMarks(n.leaf.any)?.let {
                if (must) put(layer, mustAboveTail, it, aboveExclusion)
                else put(Layer.DEMAND, aboveTail, it)
            }
        } ?: return
        when (ce.toTail) {
            Tail.STAR -> {
                m.taintAlg.retainChildren(u, m.cancellation, admitsRest)?.let { kids ->
                    gateTree(kids)?.let { results.taint(layer, m.taintAlg.prepend(m, ce.toPath, it), e, c.anyTail) }
                }
                gate.taintMarks(u.leaf.exact)?.let { put(layer, Tail.EXACT, it) }
                gate.taintMarks(u.leaf.any)?.let {
                    when (c.anyTail) {
                        Tail.STAR, Tail.ANY_TAINT -> put(layer, c.anyTail, it, e.union(ce.exclusion))
                        Tail.ANY -> put(Layer.DEMAND, Tail.ANY, it)
                        else -> error("Nonexact TAINT header")
                    }
                }
            }
            else -> {
                val all = m.taintAlg.foldLeaves(u, m.cancellation, admitsRest)
                gate.taintMarks(all.exact + all.any)?.let { put(layer, ce.toTail, it, ce.toExclusion) }
            }
        }
    }

    private fun put(layer: Layer, tail: Tail, marks: MarkSet, exclusion: ExclusionSet = ExclusionSet.Empty) {
        val resultLayer = if (tail == Tail.ANY) Layer.DEMAND else layer
        if (ce.toBase == AccessPathBase.Zero) { results.reach(resultLayer); return }
        val leaf = when (tail) {
            Tail.EXACT -> m.taintLeaves(marks, MarkSet.EMPTY)
            Tail.STAR, Tail.ANY, Tail.ANY_TAINT -> m.taintLeaves(MarkSet.EMPTY, marks)
        }
        val hasExclusion = tail == Tail.STAR || tail == Tail.ANY_TAINT
        val cover = mode.run1 && hasExclusion && exclusion != ExclusionSet.Empty
        results.taint(if (cover) Layer.DEMAND else resultLayer,
            m.taintAlg.prepend(m, ce.toPath, m.taintAlg.leafNode(leaf)),
            if (cover || !hasExclusion) ExclusionSet.Empty else exclusion,
            if (tail == Tail.EXACT) Tail.ANY_TAINT else tail)
    }

    private fun gateTree(n: TaintNode): TaintNode? =
        if (ce.fromMark == MarkSlot.STAR && ce.toMark == MarkSlot.STAR) n
        else m.taintAlg.mapLeaves(n, m.cancellation) { p ->
            m.taintLeaves(gate.taintMarks(p.exact) ?: MarkSet.EMPTY, gate.taintMarks(p.any) ?: MarkSet.EMPTY)
        }

    private fun flagAtTarget(): FlowNode = FlowAlgebra.prepend(m, ce.toPath, FlowAlgebra.LEAF_NODE)
}
