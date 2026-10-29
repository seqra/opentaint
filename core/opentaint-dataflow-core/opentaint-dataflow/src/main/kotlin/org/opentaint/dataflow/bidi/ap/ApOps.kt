package org.opentaint.dataflow.bidi.ap


/** Shared facade. All walk state is local to the call. */
class ApOps(val manager: ApManager) {
    fun run1Cover(f: Facts, emit: (Facts) -> Unit) = run1CoverFacts(manager, f, emit)

    /** Scalar callers must not silently demote exact members of a mixed group. */
    fun run1Cover(f: Facts): Facts {
        var only: Facts? = null
        run1Cover(f) { value -> check(only == null) { "Mixed E-bearing facts require the callback cover" }; only = value }
        return checkNotNull(only)
    }
    fun applyEdge(c: Facts, premise: PremiseKey, e: PathEdge, statementEdge: Boolean,
                  mode: ApMode, out: ApOut, may: Boolean = false,
                  unchangedStaticInitial: InitialAp? = null, ruleAssignment: Boolean = false) {
        check(unchangedStaticInitial == null ||
            (unchangedStaticInitial === premise && unchangedStaticInitial.manager === manager)) {
            "The ordinary static gate needs this edge's original initial"
        }
        val ce = compiled(e)
        val from = (e.from.mark as? MarkSlot.Concrete)?.mark?.let { manager.marks.runtimeAtom(it, mode.markMode) }
        val assigned = (e.to.mark as? MarkSlot.Concrete)?.mark?.let { manager.marks.runtimeAtom(it, mode.markMode) }
        val protect = ruleAssignment && from != null && assigned != null &&
            (from == assigned || premise.members.any {
                (it.mark as? MarkSlot.Concrete)?.mark?.let { atom -> manager.marks.runtimeAtom(atom, mode.markMode) } == assigned && from != assigned
            })
        val sink = if (!protect) out else object : ApOut {
            override fun result(f: Facts) = out.result(manager.selectedProtection(f, manager.markSetOf(assigned!!)))
            override fun markRequest(mark: TaintMark) = out.markRequest(mark)
        }
        applyCompiledEdge(c, ce, may, staticIdentityDepth(c, premise, ce, statementEdge, mode), mode, sink,
            unchangedStaticInitial)
    }

    internal fun compiled(e: PathEdge): CompiledEdge {
        val old = e.compiled
        if (old != null && (old.toPath == null || old.toPath.manager === manager)) return old
        return manager.compile(e).also { e.compiled = it }
    }

    internal fun applyCompiledEdge(c: Facts, ce: CompiledEdge, edgeDemand: Boolean,
                                   staticAt: Int, mode: ApMode, out: ApOut,
                                   unchangedStaticInitial: InitialAp? = null) {
        manager.transportProtection(c, out) { part, sink ->
            applyCompiledEdgeRaw(part, ce, edgeDemand, staticAt, mode, sink, unchangedStaticInitial)
        }
    }

    private fun applyCompiledEdgeRaw(c: Facts, ce: CompiledEdge, edgeDemand: Boolean,
                                    staticAt: Int, mode: ApMode, out: ApOut,
                                    unchangedStaticInitial: InitialAp?) {
        manager.cancellation.checkpoint()
        if (c.base != ce.fromBase) return
        val sink = out.run1Policy(manager, mode)
        val app = EdgeApplication(manager, ce, edgeDemand, mode, sink, unchangedStaticInitial)
        when (c) {
            is Reach -> app.reach(c)
            is FlowTree -> app.flow(c, staticAt)
            is TaintTree -> app.taint(c)
        }
        app.results.flush(sink)
    }

    fun satisfying(a: Facts, j: InitialAp, mode: ApMode, record: Boolean = false): Facts? =
        satisfying(a, j.toPattern(), mode, record)

    fun satisfying(a: Facts, j: Pattern, mode: ApMode, record: Boolean = false): Facts? =
        satisfyingPart(manager, a, j, mode, record)?.let { retainProtection(a, it, manager.cancellation) }

    fun applySummary(a: Facts, j: InitialAp, g: Facts, mode: ApMode, out: ApOut,
                     original: PremiseKey? = null) {
        val masks = (g as? TaintTree)?.protectedPart()?.let { protected ->
            ProtectionOutputs(manager).also { applySummaryPart(this, a.withoutProtection(), j, protected, mode, it) }
        }
        val incoming = (j.mark as? MarkSlot.Concrete)?.mark?.let { manager.marks.runtimeAtom(it, mode.markMode) }
        var restored = MarkSet.EMPTY
        if (original != null && incoming != null) {
            for (i in original.members) {
                val origin = (i.mark as? MarkSlot.Concrete)?.mark?.let { manager.marks.runtimeAtom(it, mode.markMode) } ?: continue
                if (origin != incoming) restored += origin
            }
        }
        val restoredMarks = manager.intern(restored)
        val sink = if (masks == null && restoredMarks.isEmpty) out else object : ApOut {
            override fun result(f: Facts) {
                val flagged = masks?.attach(f) ?: f
                out.result(if (restoredMarks.isEmpty) flagged else manager.selectedProtection(flagged, restoredMarks))
            }
            override fun markRequest(mark: TaintMark) = out.markRequest(mark)
        }
        applySummaryPart(this, a, j, g, mode, sink)
    }

    fun applyRecordLeaf(a: Facts, view: RecordLeafView, nonSubsumable: Boolean,
                        mode: ApMode, out: ApOut, original: PremiseKey? = null) {
        val trigger = (view.premise.fact.mark as? MarkSlot.Concrete)?.mark
            ?.let { manager.marks.runtimeAtom(it, mode.markMode) }
        var restored = MarkSet.EMPTY
        if (original != null && trigger != null) for (i in original.members) {
            val origin = (i.mark as? MarkSlot.Concrete)?.mark
                ?.let { manager.marks.runtimeAtom(it, mode.markMode) } ?: continue
            if (origin != trigger) restored += origin
        }
        val sink = if (restored.isEmpty) out else object : ApOut {
            override fun result(f: Facts) = out.result(manager.selectedProtection(f, restored))
            override fun markRequest(mark: TaintMark) = out.markRequest(mark)
        }
        applyRecordLeafPart(this, a, view, nonSubsumable, mode, sink)
    }

    fun applyCombination(parts: List<Pair<Facts, InitialAp>>, g: TaintTree, mode: ApMode, out: ApOut) =
        applyCombinationPart(manager, parts, g, mode, out.run1Policy(manager, mode))

    /** Used only after E6's full matching and TAINT guards. Caller layers remain in the resume context. */
    internal fun applyMatchedCombination(linkLayers: List<Layer>, g: TaintTree, out: ApOut) =
        applyMatchedCombinationPart(manager, linkLayers, g, out)

    fun without(c: Facts, part: Facts): Facts? = withoutPart(manager, c, part)
    fun reverse(e: PathEdge): PathEdge? = revEdge(e)
    fun leaves(f: Facts): Sequence<Pattern> = leafViews(manager, f)
    fun leavesNear(f: Facts, p: IntArray): Sequence<Pattern> = nearLeafViews(manager, f, p)

    fun clean(c: Facts, premise: PremiseKey, cl: Cleaner, mode: ApMode, out: ApOut) {
        val protect = c.base == cl.base
        val sink = if (!protect) out else object : ApOut {
            override fun result(f: Facts) = out.result(manager.selectedProtection(f, cl.mark?.let { manager.markSetOf(manager.marks.runtimeAtom(it, mode.markMode)) }))
            override fun markRequest(mark: TaintMark) = out.markRequest(mark)
        }
        manager.transportProtection(c, sink) { part, target ->
            cleanFacts(manager, part, premise, cl, mode, target.run1Policy(manager, mode))
        }
    }

    /** Selected FULL mask; null Cleaner.mark retains its all-mark meaning on the scalar API. */
    fun cleanSelectedFullMask(c: Facts, premise: PremiseKey, geometry: Cleaner, selected: MarkSet,
                              mode: ApMode, request: (MarkSet) -> Unit, out: ApOut) {
        check(geometry.mark != null) { "A FULL cleanup block must have selected-mark geometry" }
        val sink = if (c.base != geometry.base) out else object : ApOut {
            override fun result(f: Facts) = out.result(manager.selectedProtection(f, selected))
            override fun markRequest(mark: TaintMark) = out.markRequest(mark)
        }
        val protected = (c as? TaintTree)?.protectedPart()
        val masks = protected?.let { part -> ProtectionOutputs(manager).also {
            cleanSelectedFullMask(manager, part, geometry, selected, mode, {}, it.run1Policy(manager, mode))
        } }
        val target = if (masks == null) sink else object : ApOut {
            override fun result(f: Facts) = sink.result(masks.attach(f))
            override fun markRequest(mark: TaintMark) = sink.markRequest(mark)
        }
        cleanSelectedFullMask(manager, c, geometry, selected, mode, request, target.run1Policy(manager, mode))
    }

    fun filter(c: Facts, f: TypeFilter): Facts? = filterFacts(manager, c, f)?.let { retainProtection(c, it, manager.cancellation) }
    fun limit(c: Facts, fieldLimit: Int, out: ApOut) = manager.transportProtection(c, out) { part, sink ->
        limitFacts(manager, part, fieldLimit, sink)
    }
    /** Pass the original initial only when the run-1 static catalog covers this check. */
    fun checkMark(c: Facts, p: Pattern, mode: ApMode,
                  unchangedStaticInitial: InitialAp? = null): MarkCheck =
        when (val result = markCheckFacts(manager, c, p, mode, unchangedStaticInitial)) {
            is MarkCheck.Holds -> MarkCheck.Holds(retainProtection(c, result.facts, manager.cancellation))
            else -> result
        }
    fun withoutMarks(c: Facts, marks: MarkSet): Facts? = withoutMarksPart(manager, c, marks)

    fun targetTree(target: PathFact, layer: Layer, mode: ApMode? = null): Facts {
        check(target.mark is MarkSlot.Concrete && target.tail != Tail.STAR) { "W7: a target must be concrete and exact or any" }
        val value = manager.factsOf(target, ExclusionSet.Empty, layer)
        return if (mode == null) value else manager.runtimeFact(value, mode)
    }

    fun zero(layer: Layer): Reach = Reach.of(layer)
    fun startFact(i: InitialAp): Facts = initialFacts(manager, i)
    fun startFact(i: InitialAp, mode: ApMode): Facts = manager.runtimeFact(initialFacts(manager, i), mode)
    fun runtimeFact(f: Facts, mode: ApMode): Facts = manager.runtimeFact(f, mode)
    fun policy(added: Facts): InitialAp = policyInitial(manager, added)
    fun emit(d: DemandPattern, added: Facts, policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = manager.marks)): List<InitialAp> = emitInitials(this, d, added, policy)
    fun restrictReference(j: InitialAp, g: Facts, d: DemandPattern): List<Conclusion> = restrictRaw(this, j, g, d)
    fun restrict(j: InitialAp, g: Facts, d: DemandPattern, policy: RestrictedInitialPolicy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = manager.marks)): List<Facts> = restrictFacts(this, j, g, d, policy)
    fun demandPart(premise: PremiseKey, g: Facts, direction: Direction): Facts? =
        selectDemand(manager, premise, g, direction)
}

private fun staticIdentityDepth(c: Facts, premise: PremiseKey, ce: CompiledEdge,
                                statementEdge: Boolean, mode: ApMode): Int {
    if (c !is FlowTree || c.layer != Layer.NORMAL || !mode.run1 || !statementEdge) return -1
    if (c.base != STATIC || ce.fromBase != STATIC) return -1
    val i = premise as? InitialAp ?: return -1
    if (i.base != STATIC || i.tail != Tail.STAR || i.mark != MarkSlot.STAR) return -1
    val q = i.pathData
    if (!(q.isEmpty() || (q.size == 1 && q[0].isClass()))) return -1
    if (ce.fromPathData.size <= q.size || !ce.fromPathData.startsWith(q)) return -1
    return q.size
}
