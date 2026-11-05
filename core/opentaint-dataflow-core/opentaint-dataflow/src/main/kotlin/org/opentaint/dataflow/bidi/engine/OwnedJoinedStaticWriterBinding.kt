package org.opentaint.dataflow.bidi.engine

import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.OwnedScope
import org.opentaint.dataflow.bidi.store.StaticWriteKeyInterner

/** Only an existing live input link can bind a primitive writer. */
internal sealed interface OwnedWriterInputKey {
    data class Local(val link: LocalLink) : OwnedWriterInputKey
    data class Call(val ref: CallerRef, val zeroOnly: Boolean) : OwnedWriterInputKey
}

internal class OwnedWriterInput private constructor(
    val parent: OwnedScope,
    val original: InitialAp,
    val actual: Facts,
    val key: OwnedWriterInputKey,
    val zeroOnly: Boolean,
) {
    companion object {
        fun local(method: MethodKey, link: LocalLink, actual: Facts): OwnedWriterInput =
            OwnedWriterInput(OwnedScope(method, link.parent),
                checkNotNull(link.original as? InitialAp) { "Run-1 local originals are singleton" }, actual,
                OwnedWriterInputKey.Local(link), zeroOnly = false)

        fun call(part: Subscription): OwnedWriterInput =
            OwnedWriterInput(OwnedScope(part.ref.caller, part.ref.scope),
                checkNotNull(part.ref.premise as? InitialAp) { "Run-1 caller originals are singleton" }, part.added,
                OwnedWriterInputKey.Call(part.ref, part.zeroOnly), part.zeroOnly)
    }
}

/** Joined phase A. Bind local inputs first, then real method callers at the root.
 *
 * It borrows existing current inputs after all runners join. No second standing input store,
 * synthetic method, alias application, static composition or new request authority is added.
 */
internal class OwnedJoinedStaticWriterBinding(
    private val ops: ApOps,
    private val mode: ApMode,
    private val keys: StaticWriteKeyInterner,
    private val borrow: (OwnedScope, Publication, (OwnedWriterInput) -> Unit) -> Unit,
    private val onBound: (OwnedScope, InitialAp, Pattern) -> Unit,
    private val checkpoint: () -> Unit,
) {
    private data class Writer(val owner: OwnedScope, val id: Int)
    private data class InputKey(val key: OwnedWriterInputKey, val group: GroupKey)
    private val admitted = HashMap<OwnedScope, IntOpenHashSet>()
    private val pending = ArrayDeque<Writer>()
    private var offers = 0L
    private var processed = 0L
    private var candidates = 0L
    private var matchedInputs = 0L
    private var duplicateInputs = 0L
    private var outputs = 0L

    init { check(mode.run1) }

    fun offer(owner: OwnedScope, id: Int) {
        checkpoint()
        val row = keys.row(id)
        if (!RuntimeDataDomain.initial(row.original) || !RuntimeDataDomain.base(row.result.fact.base)) return
        check(row.result.fact.base == STATIC)
        check(row.original.base != STATIC) { "Static originals enter the frozen bridge graph, never writer binding" }
        offers++
        if (admitted.getOrPut(owner, ::IntOpenHashSet).add(id)) pending += Writer(owner, id)
    }

    fun complete(): JoinedStaticWriterBinding.Statistics {
        val ap = ops.manager
        while (pending.isNotEmpty()) {
            checkpoint()
            val writer = pending.removeFirst()
            val row = keys.row(writer.id)
            val conclusion = ap.factsOf(row.result.fact, row.result.exclusion, Layer.DEMAND)
            val publication = Publication(row.original, conclusion)
            val visited = HashSet<InputKey>()
            processed++
            borrow(writer.owner, publication) { input ->
                checkpoint()
                if (!RuntimeDataDomain.packet(input.original, input.actual)) return@borrow
                check((input.actual is FlowTree) == input.original.isFlow)
                candidates++
                if (!visited.add(InputKey(input.key, input.actual.groupKey))) {
                    duplicateInputs++
                    return@borrow
                }
                // Do not turn an arbitrary reached ZERO packet into a new source authority.
                if (row.original.isZero && (!input.original.isZero || input.actual !is Reach)) return@borrow
                val packets = if (input.zeroOnly) listOfNotNull(input.actual.takeIf { row.original.isZero })
                    else ap.canonicalPackets(input.actual).mapNotNull {
                        ops.matchSummary(it, row.original, mode, nativeRecordRead = false,
                            role = SummaryMatchRole.CURRENT)
                    }
                if (packets.isEmpty()) return@borrow
                matchedInputs++
                val out = object : ApOut {
                    override fun result(f: Facts) {
                        checkpoint()
                        check(f.base == STATIC)
                        // This is the existing static-result lane. Keep raw mx until AP
                        // application ends; no configured call suffix or aliases execute.
                        ops.run1Cover(f.withLayer(Layer.DEMAND)) { covered ->
                            ops.limit(covered, mode.fieldLimit, object : ApOut {
                                override fun result(f: Facts) {
                                    ops.run1Cover(f.withLayer(Layer.DEMAND)) { bounded ->
                                        for (piece in ops.leaves(bounded)) {
                                            checkpoint()
                                            outputs++
                                            onBound(input.parent, input.original, piece)
                                            if (input.original.base != STATIC)
                                                offer(input.parent, keys.intern(input.original, piece))
                                        }
                                    }
                                }
                                override fun markRequest(mark: TaintMark) =
                                    error("A joined field cut cannot create a mark request")
                            })
                        }
                    }
                    // Live execution already owns the exclusion's request.
                    override fun markRequest(mark: TaintMark) = Unit
                }
                if (input.zeroOnly) out.result(conclusion)
                else for (actual in packets) ops.applySummary(actual, row.original, conclusion, mode, out, original = input.original)
            }
        }
        checkpoint()
        return JoinedStaticWriterBinding.Statistics(offers, admitted.values.sumOf { it.size.toLong() }, processed,
            candidates, duplicateInputs, matchedInputs, outputs)
    }
}
