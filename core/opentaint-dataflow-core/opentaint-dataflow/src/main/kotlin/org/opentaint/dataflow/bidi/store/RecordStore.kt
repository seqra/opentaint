package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.graph.PortId
import org.opentaint.dataflow.graph.BlockId

/** An admitted normal singleton summary, retained in the direction in which it was derived. */
class Record(
    val method: MethodKey,
    val direction: Direction,
    val premise: InitialAp,
    val conclusion: Facts,
    val scope: BlockScope? = null,
    val exit: PortId? = null,
) {
    init { require((scope == null) == (exit == null)) { "A scoped native record keeps both control ports" } }

    /** AP reversal is below; reverse the control ports independently. */
    fun scopeIn(direction: Direction): BlockScope? = scope?.let {
        if (direction == this.direction) it else BlockScope(it.block, checkNotNull(exit))
    }
    fun exitIn(direction: Direction): PortId? = scope?.let {
        if (direction == this.direction) exit else it.entry
    }
    /** Transient opposite-direction reads retain their actual premise and result layer. */
    private fun nativeReversedLeavesAt(a: Pattern): Sequence<Pair<NativeReverseRead, Boolean>> = sequence {
        val m = premise.manager
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(premise, conclusion) || !RuntimeDataDomain.base(a.fact.base)) return@sequence
        check(conclusion.layer == Layer.NORMAL) { "Only a normal native record has reversed views" }
        val nativePremise = premise.toPattern()
        for (leaf in ApOps(m).leaves(conclusion)) {
            m.cancellation.checkpoint()
            if (leaf.fact.base != a.fact.base ||
                !(leaf.fact.path.startsWith(a.fact.path) || a.fact.path.startsWith(leaf.fact.path))) continue
            reverseNativeOne(leaf, nativePremise)?.let { yield(it) }
        }
    }

    /** Metadata is an invocation annotation, not part of RecordLeafView equality. */
    fun forEachReversedAt(a: Pattern, emit: (RecordLeafView, Boolean) -> Unit) {
        forEachNativeReversedAt(a) { read, protected -> emit(read.view, protected) }
    }

    fun forEachNativeReversedAt(a: Pattern, emit: (NativeReverseRead, Boolean) -> Unit) {
        for ((read, protected) in nativeReversedLeavesAt(a)) emit(read, protected)
    }

    /** Read-only geometry view for diagnostic and reference clients. */
    fun reversedAt(a: Pattern): Sequence<RecordLeafView> = nativeReversedLeavesAt(a).map { it.first.view }

    internal fun reverseOne(leaf: Pattern, nativePremise: Pattern): Pair<RecordLeafView, Boolean>? {
        return reverseNativeOne(leaf, nativePremise)?.let { it.first.view to it.second }
    }

    internal fun reverseNativeOne(leaf: Pattern, nativePremise: Pattern): Pair<NativeReverseRead, Boolean>? {
        val m = premise.manager
        val view = reverseNativeRecordLeaf(direction, nativePremise, Conclusion(leaf.fact, leaf.exclusion, demand = false))
            ?: return null
        var at: TaintNode? = (conclusion as? TaintTree)?.nonSubsumable
        for (accessor in leaf.fact.path) { m.cancellation.checkpoint(); at = at?.child(accessor) }
        val atom = (leaf.fact.mark as? MarkSlot.Concrete)?.mark
        val protected = atom != null && at?.leaf?.let {
            atom in if (leaf.fact.tail == Tail.EXACT) it.exact else it.any
        } == true
        return view to protected
    }
}

/** One actual output position, not a full-mark posting. Record identity is unchanged. */
class RecordOutputPosition internal constructor(val record: Record, private val node: PathNode?, val ordinal: Int) {
    val path: List<Int> get() = node?.toList() ?: emptyList()
    fun forEachReversedAt(actual: Pattern, emit: (RecordLeafView, Boolean) -> Unit) {
        forEachNativeReversedAt(actual) { read, protected -> emit(read.view, protected) }
    }
    fun forEachNativeReversedAt(actual: Pattern, emit: (NativeReverseRead, Boolean) -> Unit) {
        val m = record.premise.manager
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(record.premise, record.conclusion) || actual.fact.base != record.conclusion.base) return
        val p = path
        if (!(p.startsWith(actual.fact.path) || actual.fact.path.startsWith(p))) return
        check(record.conclusion.layer == Layer.NORMAL)
        val nativePremise = record.premise.toPattern()
        fun offer(pattern: Pattern) { record.reverseNativeOne(pattern, nativePremise)?.let { (view, protected) -> emit(view, protected) } }
        when (val value = record.conclusion) {
            is Reach -> if (p.isEmpty()) offer(m.zero.toPattern())
            is FlowTree -> {
                var at: FlowNode? = value.root
                for (accessor in p) { m.cancellation.checkpoint(); at = at?.child(accessor) }
                if (at?.leaf?.isEmpty == false)
                    offer(Pattern(PathFact(value.base, p, value.tail, MarkSlot.Star(value.markExclusion)), value.exclusion))
            }
            is TaintTree -> {
                var at: TaintNode? = value.root
                for (accessor in p) { m.cancellation.checkpoint(); at = at?.child(accessor) }
                val leaf = at?.leaf ?: return
                for (id in leaf.exact.data) {
                    m.cancellation.checkpoint()
                    offer(Pattern(PathFact(value.base, p, Tail.EXACT, MarkSlot.Concrete(TaintMark(id))), ExclusionSet.Empty))
                }
                for (id in leaf.any.data) {
                    m.cancellation.checkpoint()
                    offer(Pattern(PathFact(value.base, p, value.anyTail, MarkSlot.Concrete(TaintMark(id))), value.exclusion))
                }
            }
        }
    }
    override fun equals(other: Any?): Boolean = other is RecordOutputPosition && record === other.record && ordinal == other.ordinal
    override fun hashCode(): Int = 31 * System.identityHashCode(record) + ordinal
}

/** Persistent native records. A run obtains a view that permits reads only. */
interface RecordStore {
    fun add(record: Record)
    fun byEntry(method: MethodKey, addedFact: Pattern): Sequence<Record>
    fun byExit(method: MethodKey, fact: Pattern): Sequence<Record>
    fun byEntry(method: MethodKey, scope: BlockScope, addedFact: Pattern): Sequence<Record> = emptySequence()
    fun byExit(method: MethodKey, scope: BlockScope, fact: Pattern): Sequence<Record> = emptySequence()
    fun byExitPositions(method: MethodKey, scope: BlockScope, fact: Pattern): List<RecordOutputPosition>? = null
    fun view(): RecordStore
    fun persist(direction: Direction, summaries: Sequence<Pair<MethodKey, RunSummaryStore>>)
    fun persistScoped(direction: Direction, summaries: Sequence<ScopedRunSummary>) {
        check(!summaries.iterator().hasNext()) { "This record store does not support scoped persistence" }
    }
    fun persistCompleted(direction: Direction, summaries: Sequence<Pair<MethodKey, RunSummaryStore>>,
                         scoped: Sequence<ScopedRunSummary>) {
        persist(direction, summaries)
        persistScoped(direction, scoped)
    }
}

data class ScopedRunSummary(val key: ScopedSummaryKey, val summaries: RunSummaryStore)

/** The driver writes only at a barrier; the next run reads the published indexes. */
class PersistentRecordStore(private val m: ApManager) : RecordStore {
    private data class Owner(val method: MethodKey, val direction: Direction,
                             val scope: BlockScope?, val exit: PortId?)
    private data class ScopedIndexKey(val method: MethodKey, val block: BlockId, val port: PortId)
    private data class Signature(val owner: Owner, val initial: InitialAp, val facts: Facts,
                                 val protection: TaintNode?)
    private class Indexes {
        val entry = HashMap<MethodKey, PathTrie<Record>>()
        val exit = HashMap<MethodKey, PathTrie<RecordOutputPosition>>()
        val scopedEntry = HashMap<ScopedIndexKey, PathTrie<Record>>()
        val scopedExit = HashMap<ScopedIndexKey, PathTrie<RecordOutputPosition>>()
        val records = HashMap<Signature, Record>()
    }
    private class State(val current: LinkedHashMap<Owner, RunSummaryStore>, val indexes: Indexes)
    private var state = State(LinkedHashMap(), Indexes())
    private val current get() = state.current
    private val indexes get() = state.indexes

    private fun signature(owner: Owner, initial: InitialAp, facts: Facts) =
        Signature(owner, initial, facts, (facts as? TaintTree)?.nonSubsumable)

    private fun ingest(owner: Owner, premise: InitialAp, facts: Facts,
                       staged: MutableMap<Owner, RunSummaryStore>, copied: MutableSet<Owner>): Boolean {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(premise, facts)) return false
        checkNativeRecord(owner.direction, premise, facts)
        if (copied.add(owner)) {
            val replacement = RunSummaryStore(m)
            for ((initial, value) in current[owner]?.all() ?: emptySequence())
                replacement.addAdmittedAll(initial, value)
            staged[owner] = replacement
        }
        return staged.getValue(owner).addAdmittedAll(premise, facts).isNotEmpty()
    }

    private fun mutation(supplied: Map<Signature, Record> = emptyMap(),
                         body: (MutableMap<Owner, RunSummaryStore>, MutableSet<Owner>) -> Boolean) {
        m.cancellation.checkpoint()
        val staged = LinkedHashMap(current)
        if (!body(staged, HashSet())) return
        val next = rebuild(staged, supplied)
        m.cancellation.checkpoint()
        state = State(staged, next)
    }

    override fun add(record: Record) {
        val owner = Owner(record.method, record.direction, record.scope, record.exit)
        mutation(mapOf(signature(owner, record.premise, record.conclusion) to record)) { staged, copied ->
            ingest(owner, record.premise, record.conclusion, staged, copied)
        }
    }

    /** Build a complete current directory; old delta Records cease to be authoritative. */
    private fun rebuild(staged: Map<Owner, RunSummaryStore>, supplied: Map<Signature, Record>): Indexes {
        val old = indexes
        val next = Indexes()
        for ((owner, store) in staged) for ((premise, facts) in store.all()) {
            m.cancellation.checkpoint()
            val initial = premise as InitialAp
            val key = signature(owner, initial, facts)
            val record = old.records[key] ?: supplied[key] ?:
                Record(owner.method, owner.direction, initial, facts, owner.scope, owner.exit)
            next.records[key] = record
            val input = if (owner.scope == null)
                next.entry.getOrPut(owner.method) { PathTrie(m.cancellation) }
            else next.scopedEntry.getOrPut(ScopedIndexKey(owner.method, owner.scope.block, owner.scope.entry)) {
                PathTrie(m.cancellation)
            }
            input.add(initial.base, initial.pathData, record)
            val output = if (owner.scope == null)
                next.exit.getOrPut(owner.method) { PathTrie(m.cancellation) }
            else next.scopedExit.getOrPut(ScopedIndexKey(owner.method, owner.scope.block, checkNotNull(owner.exit))) {
                PathTrie(m.cancellation)
            }
            var ordinal = 0
            m.forEachLeafPosition(facts) { base, path ->
                output.add(base, path, RecordOutputPosition(record, m.path(path.asList()), ordinal++))
            }
        }
        return next
    }

    override fun byEntry(method: MethodKey, addedFact: Pattern): Sequence<Record> = sequence {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.base(addedFact.fact.base)) return@sequence
        for (record in indexes.entry[method]?.around(addedFact.fact.base, addedFact.fact.path.toIntArray()).orEmpty()) {
            m.cancellation.checkpoint()
            yield(record)
        }
    }

    override fun byExit(method: MethodKey, fact: Pattern): Sequence<Record> = sequence {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.base(fact.fact.base)) return@sequence
        val seen = HashSet<Record>()
        for (position in indexes.exit[method]?.around(fact.fact.base, fact.fact.path.toIntArray()).orEmpty()) {
            m.cancellation.checkpoint()
            if (seen.add(position.record)) yield(position.record)
        }
    }

    override fun byEntry(method: MethodKey, scope: BlockScope, addedFact: Pattern): Sequence<Record> =
        scopedCandidates(indexes.scopedEntry[ScopedIndexKey(method, scope.block, scope.entry)], addedFact)

    override fun byExit(method: MethodKey, scope: BlockScope, fact: Pattern): Sequence<Record> = sequence {
        val seen = HashSet<Record>()
        for (position in byExitPositions(method, scope, fact)) if (seen.add(position.record)) yield(position.record)
    }

    override fun byExitPositions(method: MethodKey, scope: BlockScope, fact: Pattern): List<RecordOutputPosition> {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.base(fact.fact.base)) return emptyList()
        return indexes.scopedExit[ScopedIndexKey(method, scope.block, scope.entry)]
            ?.around(fact.fact.base, fact.fact.path.toIntArray()).orEmpty()
    }

    private fun scopedCandidates(index: PathTrie<Record>?, fact: Pattern): Sequence<Record> = sequence {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.base(fact.fact.base)) return@sequence
        val seen = HashSet<Record>()
        for (record in index?.around(fact.fact.base, fact.fact.path.toIntArray()).orEmpty()) {
            m.cancellation.checkpoint()
            if (seen.add(record)) yield(record)
        }
    }

    override fun view(): RecordStore = object : RecordStore by this {
        override fun add(record: Record) = error("Read-only during a run (analyzer-core.md A4)")
        override fun persist(direction: Direction, summaries: Sequence<Pair<MethodKey, RunSummaryStore>>) =
            error("Read-only during a run (analyzer-core.md A4)")
        override fun persistScoped(direction: Direction, summaries: Sequence<ScopedRunSummary>): Unit =
            error("Read-only during a run (analyzer-core.md A4)")
        override fun persistCompleted(direction: Direction, summaries: Sequence<Pair<MethodKey, RunSummaryStore>>,
                                      scoped: Sequence<ScopedRunSummary>): Unit =
            error("Read-only during a run (analyzer-core.md A4)")
        override fun view(): RecordStore = this
    }

    override fun persist(direction: Direction, summaries: Sequence<Pair<MethodKey, RunSummaryStore>>) {
        mutation { staged, copied ->
            var changed = false
            for ((method, store) in summaries)
                changed = ingestStore(Owner(method, direction, null, null), store, staged, copied) || changed
            changed
        }
    }

    override fun persistScoped(direction: Direction, summaries: Sequence<ScopedRunSummary>) {
        mutation { staged, copied ->
            var changed = false
            for ((key, store) in summaries)
                changed = ingestStore(Owner(key.method, direction, key.scope, key.exit), store, staged, copied) || changed
            changed
        }
    }

    override fun persistCompleted(direction: Direction, summaries: Sequence<Pair<MethodKey, RunSummaryStore>>,
                                  scoped: Sequence<ScopedRunSummary>) {
        mutation { staged, copied ->
            var changed = false
            for ((method, store) in summaries)
                changed = ingestStore(Owner(method, direction, null, null), store, staged, copied) || changed
            for ((key, store) in scoped)
                changed = ingestStore(Owner(key.method, direction, key.scope, key.exit), store, staged, copied) || changed
            changed
        }
    }

    private fun ingestStore(owner: Owner, store: RunSummaryStore,
                            staged: MutableMap<Owner, RunSummaryStore>, copied: MutableSet<Owner>): Boolean {
        var changed = false
        for ((premise, facts) in store.all()) {
            m.cancellation.checkpoint()
            if (!RuntimeDataDomain.packet(premise, facts) || facts.layer == Layer.DEMAND) continue
            val initial = premise as? InitialAp ?: continue
            if (owner.direction == Direction.BACKWARD && initial.isZero) continue
            changed = ingest(owner, initial, facts, staged, copied) || changed
        }
        return changed
    }

}

private fun checkNativeRecord(direction: Direction, premise: InitialAp, conclusion: Facts) {
    assertCanonicalFlowSummary(premise, conclusion)
    check(conclusion.base !is AccessPathBase.CleanerTemporary) { "A field-action temporary cannot enter a native record" }
    check(conclusion.layer == Layer.NORMAL) { "R1: a native record must be normal" }
    check((conclusion is FlowTree) == premise.isFlow) { "K6: the conclusion kind follows the native premise" }
    check(premise.isZero || when (premise.mark) {
        is MarkSlot.Concrete -> premise.tail != Tail.STAR
        is MarkSlot.Star -> premise.tail == Tail.STAR || premise.tail == Tail.ANY_TAINT
    }) { "A native record needs a zero, concrete exact/any or abstract STAR initial" }
    if (direction == Direction.BACKWARD) {
        check(!premise.isZero) { "R1: a backward zero-premise edge is not a native record" }
        check(premise.tail != Tail.ANY_TAINT) { "W8 (d): a backward record cannot have a must premise" }
        check(conclusion !is TaintTree || !conclusion.root.hasAny) { "W6: a backward any leaf is demand" }
    }
}
