package org.opentaint.dataflow.bidi.engine

import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.StaticWriteKeyInterner

/** Phase A only: primitive and recursively caller-bound writers. Static-path
 * composition belongs to the frozen completion builder and cannot enter here. */
internal class JoinedStaticWriterBinding(
    private val ops: ApOps,
    private val mode: ApMode,
    private val keys: StaticWriteKeyInterner,
    private val borrow: (MethodKey, Publication, (Subscription) -> Unit) -> Unit,
    private val onBound: (MethodKey, InitialAp, Pattern) -> Unit,
    private val checkpoint: () -> Unit,
) {
    private data class Writer(val owner: MethodKey, val id: Int)
    private data class InputKey(val ref: CallerRef, val group: GroupKey, val zeroOnly: Boolean)
    private val admitted = HashMap<MethodKey, IntOpenHashSet>()
    private val pending = ArrayDeque<Writer>()
    private var offers = 0L
    private var processed = 0L
    private var candidates = 0L
    private var matchedInputs = 0L
    private var duplicateInputs = 0L
    private var outputs = 0L

    init { check(mode.run1) }

    fun offer(owner: MethodKey, id: Int) {
        checkpoint()
        val row = keys.row(id)
        check(row.result.fact.base == STATIC)
        check(row.original.base != STATIC) { "Static originals enter B, never BIND-W" }
        offers++
        if (admitted.getOrPut(owner, ::IntOpenHashSet).add(id)) pending += Writer(owner, id)
    }

    fun complete(): Statistics {
        val ap = ops.manager
        while (pending.isNotEmpty()) {
            checkpoint()
            val writer = pending.removeFirst()
            val row = keys.row(writer.id)
            val conclusion = ap.factsOf(row.result.fact, row.result.exclusion, Layer.DEMAND)
            val publication = Publication(row.original, conclusion)
            val visited = HashSet<InputKey>()
            processed++
            borrow(writer.owner, publication) { part ->
                checkpoint()
                check(part.callee == writer.owner) { "A writer can bind only its complete callee key" }
                check(part.ref.premise is InitialAp) { "Run-1 caller originals are singleton" }
                check((part.added is FlowTree) == part.ref.premise.isFlow)
                candidates++
                // The joined current inputs cannot grow. Admit the complete
                // call/stage/group membership once before AP application.
                if (!visited.add(InputKey(part.ref, part.added.groupKey, part.zeroOnly))) {
                    duplicateInputs++
                    return@borrow
                }
                if (row.original.isZero && (!part.ref.premise.isZero || part.added !is Reach))
                    return@borrow
                val actual = matches(part, publication, 0, ops, mode) ?: return@borrow
                matchedInputs++
                val out = object : ApOut {
                    override fun result(f: Facts) {
                        checkpoint()
                        check(f.base == STATIC)
                        // Mirror the existing static-result lane: projection,
                        // run-1 cover, cut, then cover. No alias/call suffix runs.
                        ops.run1Cover(f.withLayer(Layer.DEMAND)) { covered ->
                            ops.limit(covered, mode.fieldLimit, object : ApOut {
                                override fun result(f: Facts) {
                                    ops.run1Cover(f.withLayer(Layer.DEMAND)) { bounded ->
                                        for (piece in ops.leaves(bounded)) {
                                            checkpoint()
                                            val original = part.ref.premise
                                            outputs++
                                            onBound(part.ref.caller, original, piece)
                                            if (original.base != STATIC)
                                                offer(part.ref.caller, keys.intern(original, piece))
                                        }
                                    }
                                }
                                override fun markRequest(mark: TaintMark) =
                                    error("A joined field cut cannot create a mark request")
                            })
                        }
                    }
                    // The live exclusion operation already emitted its request.
                    // AP can report that obligation again when a raw mx-bearing
                    // FLOW image is applied. Keep mx for actual matching/output,
                    // but this guide-only phase has no new request authority.
                    override fun markRequest(mark: TaintMark) = Unit
                }
                if (part.zeroOnly) out.result(conclusion)
                else ops.applySummary(actual, row.original, conclusion, mode, out, original = part.ref.premise)
            }
        }
        checkpoint()
        return Statistics(offers, admitted.values.sumOf { it.size.toLong() }, processed,
            candidates, duplicateInputs, matchedInputs, outputs)
    }

    data class Statistics(val writerOffers: Long, val admittedWriters: Long, val processedWriters: Long,
                          val candidateInputs: Long, val duplicateInputs: Long,
                          val matchedInputs: Long, val boundOutputs: Long)
}
