package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*

/** A genuine mark request can cross a local boundary whose parent origin is static.
 * The reply resumes that boundary, not an invented instruction or a method entry.
 */
internal class LocalStaticInputRequests(
    private val ops: ApOps,
    private val mode: ApMode,
    private val owner: MethodKey,
    private val ticket: () -> Long,
    private val interest: (StaticInterest) -> Unit,
    private val resume: (LocalLink, PremiseKey, Facts) -> Unit,
) {
    private val ap get() = ops.manager
    private data class Key(val link: LocalLink, val original: InitialAp, val base: org.opentaint.dataflow.ap.ifds.AccessPathBase,
                           val tail: Tail, val exclusion: ExclusionSet, val layer: Layer)
    private class Row(val id: Long, val key: Key) {
        val pending = LinkedHashMap<TaintMark, FlowNode>()
    }
    private val byKey = HashMap<Key, Row>()
    private val byId = HashMap<Long, Row>()

    init { check(mode.run1) }

    fun request(link: LocalLink, input: FlowTree, mark: TaintMark) {
        ap.cancellation.checkpoint()
        val initial = link.original as? InitialAp ?: error("Run-1 has a singleton local origin")
        check(initial.base == STATIC && initial.mark is MarkSlot.Star)
        validateRun1Initial(initial, mode.fieldLimit)
        val key = Key(link, initial, input.base, input.tail, input.exclusion, input.layer)
        val row = byKey.getOrPut(key) { Row(ticket(), key).also { byId[it.id] = it } }
        val atom = ap.marks.runtimeAtom(mark, mode.markMode)
        val old = row.pending[atom]
        row.pending[atom] = if (old == null) input.root else FlowAlgebra.mergeAdd(old, input.root, ap.cancellation)
        if (old == null) interest(StaticInterest(owner, row.id, initial.toPattern(), MarkSet.of(atom)))
    }

    /** False means that the ticket belongs to the ordinary physical-point directory. */
    fun answer(effect: StaticOwnerEffect): Boolean {
        if (effect !is StaticOwnerEffect.PointReady) return false
        val row = byId[effect.id] ?: return false
        check(effect.owner == owner)
        val detached = ArrayList<Pair<TaintMark, FlowNode>>()
        effect.supply.groups.forEach { mark ->
            ap.cancellation.checkpoint()
            detached += mark to checkNotNull(row.pending.remove(mark)) { "A static boundary reply must answer a pending mark" }
        }
        if (row.pending.isEmpty()) {
            check(byId.remove(row.id) === row)
            check(byKey.remove(row.key) === row)
        }
        // Detach before delivery: a later exclusion at this boundary is a new request.
        for ((mark, images) in detached) {
            val actual = ap.factsOf(effect.supply.region.fact.copy(mark = MarkSlot.Concrete(mark)),
                effect.supply.region.exclusion, Layer.DEMAND)
            for (leaf in ops.leaves(actual)) {
                val concrete = concreteStaticResumeInitial(ap, leaf)
                materializeStaticFlowImages(ops, mode, row.key.original, concrete, images,
                    row.key.base, row.key.tail, row.key.exclusion, row.key.layer) { value ->
                    resume(row.key.link.copy(original = concrete, layer = value.layer), concrete, value)
                }
            }
        }
        return true
    }

    fun clear() { byId.clear(); byKey.clear() }
}

/** Shared by physical-point and local-boundary replies. This is the existing run-1 grammar. */
internal fun concreteStaticResumeInitial(ap: ApManager, leaf: Pattern): InitialAp {
    val path = leaf.fact.path
    check(path.size != 1 || leaf.fact.tail == Tail.EXACT) { "A global class-marker reply must remain exact" }
    val exact = leaf.fact.tail == Tail.EXACT
    return ap.initial(Pattern(leaf.fact.copy(path = if (path.size > 2) path.take(2) else path,
        tail = if (exact && path.size <= 2) Tail.EXACT else Tail.STAR), ExclusionSet.Empty))
}

/** Clear mx only during the same materialization operation used by Run1PointResume. */
internal fun materializeStaticFlowImages(
    ops: ApOps, mode: ApMode, abstractInitial: InitialAp, concreteInitial: InitialAp,
    images: FlowNode, base: org.opentaint.dataflow.ap.ifds.AccessPathBase, tail: Tail,
    exclusion: ExclusionSet, layer: Layer, emit: (Facts) -> Unit,
) {
    val ap = ops.manager
    FlowAlgebra.forEachLeaf(images, EMPTY_PATH, ap.cancellation) { path, _ ->
        val root = FlowAlgebra.prepend(ap, ap.path(path), FlowAlgebra.LEAF_NODE)
        val relation = ap.flowTree(base, layer, exclusion, MarkExclusions.EMPTY, root, tail)
        ops.applySummary(ops.startFact(concreteInitial, mode), abstractInitial, relation, mode, object : ApOut {
            override fun result(f: Facts) = emit(f)
            override fun markRequest(mark: TaintMark) = Unit
        })
    }
}
