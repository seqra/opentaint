package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.Record

/** AP results only. The owner decides whether to deliver, observe, request or publish them. */
internal interface LocalRelationOut {
    fun data(original: PremiseKey, value: Facts)
    fun target(original: PremiseKey, target: Target)
    fun markRequest(mark: TaintMark)
}

/** One fully matched ND arm. The caller must join every required arm before applying it. */
internal data class LocalRelationBinding(val original: PremiseKey, val initial: InitialAp, val matched: TaintTree)

internal data class NativeRecordLane(val actual: Facts, val pendingDemotion: Boolean)

/** Input was selected with the native record matcher. Real calls retain their action suffix;
 * local boundaries commit pending demotion immediately, but both use these exact input lanes. */
internal fun nativeRecordLanes(ops: ApOps, mode: ApMode, matchedActual: Facts,
                               initial: InitialAp): List<NativeRecordLane> {
    ops.manager.cancellation.checkpoint()
    if (initial.tail != Tail.ANY_TAINT) return listOf(NativeRecordLane(matchedActual, false))
    check(mode.direction == Direction.FORWARD) { "A native must record is only forward" }
    val inside = ops.satisfying(matchedActual, initial, mode)
    val residual = if (inside == null) matchedActual else ops.without(matchedActual, inside)
    return listOfNotNull(inside?.let { NativeRecordLane(it, false) }, residual?.let { NativeRecordLane(it, true) })
}

/** Shared read-only AP transfer for local links and loop observations.
 *
 * This is the relation part of real-call application: no binding stages, alias expansion, rule
 * callbacks, static supplies, current subscriptions or source-hit side effects occur here.
 * The complete parent original is passed to AP composition so cycle protection stays unchanged.
 */
internal class LocalRelationApplication(private val ops: ApOps, private val mode: ApMode) {
    private val ap get() = ops.manager

    fun applyCurrent(actual: Facts, original: PremiseKey, initial: InitialAp,
                     conclusion: Facts, out: LocalRelationOut): Boolean {
        if (!valid(actual, original, initial, conclusion)) return false
        val matched = ops.satisfying(actual, initial, mode) ?: return false
        return applyMatched(matched, original, initial, conclusion, out)
    }

    /** Match once at subscription delivery, then share this exact applicator with saved replay. */
    fun applyMatched(actual: Facts, original: PremiseKey, initial: InitialAp,
                     conclusion: Facts, out: LocalRelationOut): Boolean {
        if (!valid(actual, original, initial, conclusion)) return false
        var applied = false
        ops.applySummary(actual, initial, conclusion, mode,
            sink(original, actual, initial.isZero, pendingDemotion = false, out) { applied = true },
            original = original)
        return applied
    }

    /** Native MUST records have a definite lane and a provisional lane. With no call suffix,
     * commit the existing pending demotion at this boundary rather than after return actions. */
    fun applyRecord(actual: Facts, original: PremiseKey, record: Record, out: LocalRelationOut): Boolean {
        val initial = record.premise
        if (!valid(actual, original, initial, record.conclusion)) return false
        val offered = ops.satisfying(actual, initial, mode, record = true) ?: return false
        var applied = false
        for (lane in nativeRecordLanes(ops, mode, offered, initial))
            ops.applySummary(lane.actual, initial, record.conclusion, mode,
                sink(original, lane.actual, initial.isZero, lane.pendingDemotion, out) { applied = true },
                original = original)
        return applied
    }

    /** Opposite-direction records retain the transient native view; do not intern a MUST query. */
    fun applyRecordView(actual: Facts, original: PremiseKey, view: RecordLeafView,
                        nonSubsumable: Boolean, out: LocalRelationOut): Boolean {
        ap.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(original, actual) || !RuntimeDataDomain.base(view.premise.fact.base) ||
            !RuntimeDataDomain.base(view.result.fact.base)) return false
        val matched = ops.satisfying(actual, view.premise, mode, record = true) ?: return false
        var applied = false
        ops.applyRecordLeaf(matched, view, nonSubsumable, mode,
            sink(original, matched, view.premise.fact.base == AccessPathBase.Zero,
                pendingDemotion = false, out) { applied = true }, original = original)
        return applied
    }

    /** Actual execution is AND. Unary metadata is never passed to this complete-join transfer. */
    fun applyCombination(parts: List<LocalRelationBinding>, conclusion: TaintTree, out: LocalRelationOut) {
        require(parts.size >= 2) { "A complete ND relation needs every matched arm" }
        check(mode.direction == Direction.FORWARD && !mode.run1) { "ND summaries require a later forward run" }
        var original: PremiseKey = ap.zero
        val layers = ArrayList<Layer>(parts.size)
        for (part in parts) {
            ap.cancellation.checkpoint()
            check(RuntimeDataDomain.packet(part.original, part.matched))
            original = ap.union(original, part.original)
            layers += part.matched.layer
        }
        val completeOriginal = original
        val triggering = parts.mapNotNull { (it.initial.mark as? MarkSlot.Concrete)?.mark }
            .map { ap.marks.runtimeAtom(it, mode.markMode) }
        val restored = ap.intern(MarkSet(completeOriginal.members.mapNotNull {
            (it.mark as? MarkSlot.Concrete)?.mark?.let { atom -> ap.marks.runtimeAtom(atom, mode.markMode) }
        }.filter { origin -> triggering.any { it != origin } }.map { it.id }.toIntArray()))
        val inherited = parts.any { it.matched.nonSubsumable != null }
        ops.applyMatchedCombination(layers, conclusion, object : ApOut {
            override fun result(f: Facts) {
                val marked = if (inherited && f is TaintTree) f.withProtection(f.root, ap.cancellation) else f
                val result = ap.selectedProtection(marked, restored)
                sink(completeOriginal, conclusion, zeroPremise = false, pendingDemotion = false, out) {}.result(result)
            }
            override fun markRequest(mark: TaintMark) = out.markRequest(mark)
        })
    }

    /** The caller performs the complete ND Target join. The observer can use its selected arm
     * metadata without emitting a Target or replacing the real join by an OR. */
    fun targetArmLayer(actual: Facts, initial: InitialAp, target: Target, saved: Boolean,
                       offeredLayer: Layer = actual.layer): Layer? {
        ap.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(initial, actual)) return null
        if (mode.direction == Direction.BACKWARD && target is Target.NormalTarget) return null
        val matched = ops.satisfying(actual, initial, mode,
            record = saved && initial.tail != Tail.ANY_TAINT) ?: return null
        val layer = offeredLayer or (matched.layer == Layer.DEMAND)
        return layer.takeIf { target !is Target.NormalTarget || it == Layer.NORMAL }
    }

    private fun valid(actual: Facts, original: PremiseKey, initial: InitialAp, conclusion: Facts): Boolean {
        ap.cancellation.checkpoint()
        return RuntimeDataDomain.packet(original, actual) && RuntimeDataDomain.packet(initial, conclusion)
    }

    private fun sink(original: PremiseKey, actual: Facts, zeroPremise: Boolean,
                     pendingDemotion: Boolean, out: LocalRelationOut,
                     applied: () -> Unit): ApOut = object : ApOut {
        override fun result(f: Facts) {
            if (!RuntimeDataDomain.packet(original, actual) || !RuntimeDataDomain.packet(original, f)) return
            applied()
            fun emit(value: Facts) {
                val committed = if (pendingDemotion) value.withLayer(Layer.DEMAND) else value
                if (mode.direction == Direction.BACKWARD && !zeroPremise && committed is Reach)
                    out.target(original, Target.DemandTarget)
                else out.data(original, committed)
            }
            if (!mode.run1) emit(f) else {
                val runtime = ops.runtimeFact(f, mode)
                var staticOrigin = false
                original.forEachMember { if (it.base == STATIC) staticOrigin = true }
                val demand = runtime.base == STATIC || staticOrigin || runtime is TaintTree && mode.markMode == MarkMode.GROUP
                ops.run1Cover(if (demand) runtime.withLayer(Layer.DEMAND) else runtime, ::emit)
            }
        }
        override fun markRequest(mark: TaintMark) = out.markRequest(mark)
    }
}
