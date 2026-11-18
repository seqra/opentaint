package org.opentaint.dataflow.bidi.driver

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId

/** Private barrier keys. No comparison changes a real demand row or an AP key. */
internal data class HandoffOwner(val method: MethodKey, val scope: BlockScope? = null, val exit: PortId? = null) {
    init { check((scope == null) == (exit == null)) }
    val entryOwner: Pair<MethodKey, BlockScope?> get() = method to scope
}

internal data class HandoffC2Key(
    val owner: Pair<MethodKey, BlockScope?>,
    val protected: Boolean,
    val entry: DemandEntry,
)
internal data class HandoffC5Key(
    val owner: HandoffOwner,
    val protected: Boolean,
    val entry: DemandEntry,
    val output: DemandExit,
)

/** These adapters bind the late-FULL service laws in retained-demand-service-basis.md.
 * Full checked Pattern equality follows the hash lookup, including E/mx and full marks. */
internal class HandoffServiceKeys(private val ap: ApManager) {
    private fun point(p: Pattern): Boolean {
        val mark = p.fact.mark as? MarkSlot.Concrete ?: return false
        if (!ap.marks.isFull(mark.mark) || p.fact.tail !in setOf(Tail.STAR, Tail.EXACT)) return false
        if (p.fact.tail == Tail.EXACT && p.exclusion != ExclusionSet.Empty) return false
        return when (p.fact.base) {
            AccessPathBase.This, AccessPathBase.Return, AccessPathBase.Exception,
            is AccessPathBase.Argument, is AccessPathBase.LocalVar -> true
            AccessPathBase.ClassStatic -> p.fact.path.let { path ->
                path.size == 1 && path[0].isClass() && p.fact.tail == Tail.EXACT ||
                    path.size >= 2 && path[0].isClass() && path[1].isFieldAccessor()
            }
            else -> false
        }
    }

    fun entry(entry: DemandEntry): DemandEntry {
        val p = (entry as? DemandEntry.Data)?.pattern ?: return entry
        return if (point(p)) DemandEntry.Data(p.copy(fact = p.fact.copy(tail = Tail.EXACT),
            exclusion = ExclusionSet.Empty)) else entry
    }

    fun output(exit: DemandExit): DemandExit {
        val p = (exit as? DemandExit.Data)?.pattern ?: return exit
        return if (p.fact.tail == Tail.ANY && p.exclusion == ExclusionSet.Empty)
            DemandExit.Data(p.copy(fact = p.fact.copy(tail = Tail.STAR))) else exit
    }

    fun c2(origin: HandoffOrigin, row: PairedDemand) =
        HandoffC2Key(origin.owner.entryOwner, origin.protected, entry(row.entry))
    fun c5(origin: HandoffOrigin, row: PairedDemand) =
        HandoffC5Key(origin.owner, origin.protected, entry(row.entry), output(row.exit))

    /** Exact C5 image containment, never C2 MAY coverage. Only the same point or
     * one final counted accessor (preceded by CLASS accessors) is admitted. */
    fun c5Alternatives(key: HandoffC5Key): Sequence<HandoffC5Key> = sequence {
        yield(key)
        val p = (key.entry as? DemandEntry.Data)?.pattern ?: return@sequence
        if (!point(p)) return@sequence
        when (p.fact.base) {
            AccessPathBase.This, AccessPathBase.Return, is AccessPathBase.Argument, is AccessPathBase.LocalVar -> Unit
            else -> return@sequence
        }
        yield(key.copy(entry = DemandEntry.Data(p.copy(fact = p.fact.copy(tail = Tail.ANY)))))
        val path = p.fact.path
        if (path.isEmpty() || !path.last().isCounted()) return@sequence
        var length = path.size - 1
        while (true) {
            yield(key.copy(entry = DemandEntry.Data(p.copy(fact = p.fact.copy(path = path.take(length), tail = Tail.ANY)))))
            if (length == 0 || !path[length - 1].isClass()) break
            length--
        }
    }

    /** Stable decoded order. Comparison keys remain full native values; this string
     * only orders origins within one owner, never authorizes coverage. */
    fun order(row: PairedDemand): String = field(when (val e = row.entry) {
        is DemandEntry.Data -> "D" + order(e.pattern)
        DemandEntry.Zero -> "Z"
        DemandEntry.Target -> "T"
    }) + field(when (val e = row.exit) {
        is DemandExit.Data -> "D" + order(e.pattern)
        DemandExit.Zero -> "Z"
    })

    fun order(p: Pattern): String = field(p.fact.base.toString()) +
        field(p.fact.path.joinToString("") { field(ap.accessors.accessor(it).toString()) }) +
        field(p.fact.tail.name) + field(when (val mark = p.fact.mark) {
            is MarkSlot.Concrete -> "T" + field(ap.marks.name(mark.mark))
            is MarkSlot.Star -> "F" + mark.excluded.ids.map { ap.marks.name(TaintMark(it)) }.sorted().joinToString("") { field(it) }
        }) + field(when (val e = p.exclusion) {
            ExclusionSet.Empty -> ""
            is ExclusionSet.Concrete -> e.ids.map { ap.accessors.accessor(it).toString() }.sorted().joinToString("") { field(it) }
        })

    private fun field(value: String): String = "${value.length}:$value"
}
