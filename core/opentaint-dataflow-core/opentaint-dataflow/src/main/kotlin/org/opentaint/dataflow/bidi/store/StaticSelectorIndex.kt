package org.opentaint.dataflow.bidi.store

import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.bidi.ap.*

/** These detached keys never intern an atom or enumerate the members of a group. */
internal sealed interface StaticMarkSelector {
    data object Zero : StaticMarkSelector
    data class Full(val atom: TaintMark, val exact: ExactMark) : StaticMarkSelector
    data class Group(val id: GroupId) : StaticMarkSelector
}

internal fun MarkTable.staticSelector(atom: TaintMark): StaticMarkSelector? = when (val key = key(atom)) {
    is MarkAtomKey.Full -> StaticMarkSelector.Full(atom, key.mark)
    is MarkAtomKey.Group -> StaticMarkSelector.Group(key.id)
    MarkAtomKey.ControlZero -> null // A nonnull control atom is not an endpoint ZERO.
}

internal sealed interface StaticLabelSelection {
    data object All : StaticLabelSelection
    data object FlowOnly : StaticLabelSelection
    data class OutputCovers(val actual: StaticMarkSelector) : StaticLabelSelection
    data class OutputComposesWith(val input: StaticMarkSelector) : StaticLabelSelection
}

internal data class StaticRowQuery(
    val labels: StaticLabelSelection = StaticLabelSelection.All,
    val includeFlow: Boolean = true,
    val mappedGeometryAllowed: (Pattern) -> Boolean = { true },
) {
    companion object { val ALL = StaticRowQuery() }
}

internal fun outputCovering(actual: Pattern, marks: MarkTable): StaticLabelSelection = when (val mark = actual.fact.mark) {
    is MarkSlot.Star -> StaticLabelSelection.FlowOnly
    is MarkSlot.Concrete -> when {
        actual.fact.base == org.opentaint.dataflow.ap.ifds.AccessPathBase.Zero ->
            StaticLabelSelection.OutputCovers(StaticMarkSelector.Zero)
        else -> marks.staticSelector(mark.mark)?.let(StaticLabelSelection::OutputCovers) ?: StaticLabelSelection.All
    }
}

internal fun outputComposable(input: TaintMark?, marks: MarkTable): StaticLabelSelection =
    if (input == null) StaticLabelSelection.FlowOnly
    else marks.staticSelector(input)?.let(StaticLabelSelection::OutputComposesWith) ?: StaticLabelSelection.All

/** Sorted original ordinals. Every ordinal keeps its own complete relation and owner family. */
internal class StaticOutputOrdinals private constructor(
    val size: Int,
    val flowOrdinal: Int,
    private val full: Map<TaintMark, IntArray>?,
    private val group: Map<GroupId, IntArray>?,
    private val fullInGroup: Map<GroupId, IntArray>?,
    private val zero: IntArray?,
    private val unknown: Boolean,
) {
    /** At most two sorted postings plus FLOW. No duplicate is decoded or tested twice. */
    fun ordinals(selection: StaticLabelSelection, includeFlow: Boolean = true): IntIterator {
        if (selection == StaticLabelSelection.All || unknown && selection != StaticLabelSelection.FlowOnly)
            return object : IntIterator() {
                private var next = 0
                private fun skipFlow() { if (!includeFlow && next == flowOrdinal) next++ }
                override fun hasNext(): Boolean { skipFlow(); return next < size }
                override fun nextInt(): Int { check(hasNext()); return next++ }
            }
        var a: IntArray? = null
        var b: IntArray? = null
        when (selection) {
            StaticLabelSelection.All -> error("Handled above")
            StaticLabelSelection.FlowOnly -> Unit
            is StaticLabelSelection.OutputCovers -> when (val key = selection.actual) {
                StaticMarkSelector.Zero -> a = zero
                is StaticMarkSelector.Full -> { a = full?.get(key.atom); b = group?.get(key.exact.group) }
                is StaticMarkSelector.Group -> a = group?.get(key.id)
            }
            is StaticLabelSelection.OutputComposesWith -> when (val key = selection.input) {
                StaticMarkSelector.Zero -> Unit // Mapped relations cannot join through endpoint ZERO.
                is StaticMarkSelector.Full -> { a = full?.get(key.atom); b = group?.get(key.exact.group) }
                is StaticMarkSelector.Group -> { a = group?.get(key.id); b = fullInGroup?.get(key.id) }
            }
        }
        val first = a
        val second = b
        return object : IntIterator() {
            private var ai = 0
            private var bi = 0
            private var flow = if (includeFlow) flowOrdinal else -1
            override fun hasNext(): Boolean = ai < (first?.size ?: 0) || bi < (second?.size ?: 0) || flow >= 0
            override fun nextInt(): Int {
                check(hasNext())
                val av = first?.getOrNull(ai) ?: Int.MAX_VALUE
                val bv = second?.getOrNull(bi) ?: Int.MAX_VALUE
                val next = minOf(av, bv, if (flow >= 0) flow else Int.MAX_VALUE)
                if (av == next) ai++
                if (bv == next) bi++
                if (flow == next) flow = -1
                return next
            }
        }
    }

    fun visit(selection: StaticLabelSelection, includeFlow: Boolean = true, visit: (Int) -> Boolean): Boolean {
        val cursor = ordinals(selection, includeFlow)
        while (cursor.hasNext()) if (!visit(cursor.nextInt())) return false
        return true
    }

    class Builder(private val marks: MarkTable) {
        private var size = 0
        private var flowOrdinal = -1
        private var full: MutableMap<TaintMark, IntArrayList>? = null
        private var group: MutableMap<GroupId, IntArrayList>? = null
        private var fullInGroup: MutableMap<GroupId, IntArrayList>? = null
        private var zero: IntArrayList? = null
        private var unknown = false
        fun add(relation: GuidanceMarks) {
            val ordinal = size++
            when (relation) {
                GuidanceMarks.Flow -> { check(flowOrdinal == -1); flowOrdinal = ordinal }
                is GuidanceMarks.Mapped -> when (val output = relation.output) {
                    null -> (zero ?: IntArrayList().also { zero = it }).add(ordinal)
                    else -> when (val key = marks.staticSelector(output)) {
                        is StaticMarkSelector.Full -> {
                            val exact = full ?: HashMap<TaintMark, IntArrayList>().also { full = it }
                            exact.getOrPut(key.atom) { IntArrayList() }.add(ordinal)
                            val members = fullInGroup ?: HashMap<GroupId, IntArrayList>().also { fullInGroup = it }
                            members.getOrPut(key.exact.group) { IntArrayList() }.add(ordinal)
                        }
                        is StaticMarkSelector.Group -> {
                            val groups = group ?: HashMap<GroupId, IntArrayList>().also { group = it }
                            groups.getOrPut(key.id) { IntArrayList() }.add(ordinal)
                        }
                        else -> unknown = true
                    }
                }
            }
        }
        private fun <K> freeze(source: Map<K, IntArrayList>?): Map<K, IntArray>? = when (source?.size) {
            null, 0 -> null
            1 -> source.entries.single().let { mapOf(it.key to it.value.toIntArray()) }
            else -> source.mapValues { it.value.toIntArray() }
        }
        fun build() = StaticOutputOrdinals(size, flowOrdinal, freeze(full), freeze(group), freeze(fullInGroup),
            zero?.toIntArray(), unknown)
    }
}
