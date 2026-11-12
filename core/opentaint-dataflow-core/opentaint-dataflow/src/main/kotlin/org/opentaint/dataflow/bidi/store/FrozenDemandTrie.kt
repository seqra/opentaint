package org.opentaint.dataflow.bidi.store

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.util.Cancellation

internal enum class DemandVisit { CONTINUE, STOP }
internal enum class DemandScan { COMPLETED, STOPPED, UNSUPPORTED }

internal enum class DemandQueryKind { INITIAL_C2, OUTPUT_C5 }

/** A cursor only follows branches with a real compatible ANY witness. */
internal interface AnyDemandCursor {
    fun follow(accessor: Int): AnyDemandCursor?
    fun subtreeWitness(): Pattern?
}

internal interface EntryPrecisionView {
    fun precisionCursors(actual: Pattern, policy: RestrictedInitialPolicy): List<AnyDemandCursor>?
}

/** Snapshot-private geometry. Builder nodes never escape and are not changed after build. */
internal class FrozenDemandTrie<P : Any> private constructor(
    private val roots: Map<AccessPathBase, Node<P>>,
    private val cancellation: Cancellation?,
) {
    private class QueryWork(var nodes: Long = 0, var profiles: Long = 0, var candidates: Long = 0)
    private data class Terminal<P>(val ordinal: Int, val pattern: Pattern, val payload: P)
    private class Node<P : Any> {
        var values: LinkedHashMap<P, Terminal<P>>? = LinkedHashMap(2)
        var children: Int2ObjectOpenHashMap<Node<P>>? = null
        var nativeChildren: List<Node<P>> = emptyList()
        var profiles: Map<MarkSlot, List<Terminal<P>>> = emptyMap()
        var witnesses: Map<MarkSlot, Terminal<P>> = emptyMap()
        fun child(accessor: Int): Node<P>? = children?.get(accessor)
    }

    class Builder<P : Any>(private val cancellation: Cancellation? = null) {
        private val roots = HashMap<AccessPathBase, Node<P>>(4)
        private val nodes = ArrayList<Node<P>>()
        private var ordinal = 0
        private var built = false

        fun add(pattern: Pattern, payload: P): Boolean {
            check(!built)
            cancellation?.checkpoint()
            var node = roots.getOrPut(pattern.fact.base) { Node<P>().also(nodes::add) }
            for (accessor in pattern.fact.path) {
                cancellation?.checkpoint()
                val children = node.children ?: Int2ObjectOpenHashMap<Node<P>>().also { node.children = it }
                node = children.getOrPut(accessor) { Node<P>().also(nodes::add) }
            }
            val values = checkNotNull(node.values)
            if (values.containsKey(payload)) return false
            values[payload] = Terminal(ordinal++, pattern, payload)
            return true
        }

        fun build(): FrozenDemandTrie<P> {
            check(!built)
            built = true
            // Use the original fastutil child order, including its final hash-table capacity.
            for (node in nodes.asReversed()) {
                cancellation?.checkpoint()
                node.nativeChildren = node.children?.values?.toList().orEmpty()
                val values = checkNotNull(node.values)
                node.profiles = values.values.groupBy { it.pattern.fact.mark }
                val witnesses = LinkedHashMap<MarkSlot, Terminal<P>>()
                fun offer(mark: MarkSlot, terminal: Terminal<P>) {
                    val prior = witnesses[mark]
                    if (prior == null || terminal.ordinal < prior.ordinal) witnesses[mark] = terminal
                }
                for (terminal in values.values) {
                    val pattern = terminal.pattern
                    if (pattern.fact.tail == Tail.ANY && pattern.exclusion == ExclusionSet.Empty) {
                        offer(pattern.fact.mark, terminal)
                    }
                }
                for (child in node.nativeChildren) for ((mark, witness) in child.witnesses) offer(mark, witness)
                node.witnesses = witnesses
                node.values = null
            }
            return FrozenDemandTrie(roots, cancellation)
        }
    }

    fun hasBase(base: AccessPathBase): Boolean = roots.containsKey(base)

    fun visitNativeOrder(actual: Pattern, kind: DemandQueryKind, catalog: MarkTable?, visit: (P) -> Unit) =
        visitCountedNativeOrder(actual, kind, catalog, null, visit)

    fun visitCountedNativeOrder(actual: Pattern, kind: DemandQueryKind, catalog: MarkTable?,
                                counts: ((Long, Long, Long) -> Unit)?, visit: (P) -> Unit) {
        visitCountedUntil(actual, kind, catalog, counts) { visit(it); DemandVisit.CONTINUE }
    }

    /** One walker serves materialized C2, non-creating probes and unchanged C5. */
    fun visitCountedUntil(actual: Pattern, kind: DemandQueryKind, catalog: MarkTable?,
                          counts: ((Long, Long, Long) -> Unit)?, visit: (P) -> DemandVisit): DemandScan {
        cancellation?.checkpoint()
        var node = roots[actual.fact.base] ?: run { counts?.invoke(0, 0, 0); return DemandScan.COMPLETED }
        val work = if (counts == null) null else QueryWork()
        fun values(at: Node<P>): DemandVisit {
            if (work != null) work.nodes++
            val selected = ArrayList<Terminal<P>>()
            for ((mark, terminals) in at.profiles) {
                cancellation?.checkpoint()
                if (work != null) work.profiles++
                val compatible = when (kind) {
                    DemandQueryKind.INITIAL_C2 -> markSub(mark, actual.fact.mark, catalog)
                    DemandQueryKind.OUTPUT_C5 -> marksMeet(mark, actual.fact.mark, catalog)
                }
                if (compatible) selected.addAll(terminals)
            }
            if (selected.size > 1) selected.sortBy { it.ordinal }
            for (terminal in selected) {
                cancellation?.checkpoint()
                if (work != null) work.candidates++
                if (visit(terminal.payload) == DemandVisit.STOP) return DemandVisit.STOP
            }
            return DemandVisit.CONTINUE
        }
        try {
            for (accessor in actual.fact.path) {
                if (values(node) == DemandVisit.STOP) return DemandScan.STOPPED
                node = node.child(accessor) ?: return DemandScan.COMPLETED
            }
            // A strict descendant cannot produce a C2 primary from STAR/EXACT.
            // Companions also require that primary. MAY/MUST and C5 keep DFS.
            if (kind == DemandQueryKind.INITIAL_C2 && !actual.fact.tail.isAny) {
                return if (values(node) == DemandVisit.STOP) DemandScan.STOPPED else DemandScan.COMPLETED
            }
            val stack = ArrayDeque<Node<P>>()
            stack.addLast(node)
            while (stack.isNotEmpty()) {
                cancellation?.checkpoint()
                val at = stack.removeLast()
                if (values(at) == DemandVisit.STOP) return DemandScan.STOPPED
                stack.addAll(at.nativeChildren)
            }
            return DemandScan.COMPLETED
        } finally { if (work != null) counts?.invoke(work.nodes, work.profiles, work.candidates) }
    }

    fun precisionCursors(actual: Pattern, catalog: MarkTable?): List<AnyDemandCursor> {
        val root = roots[actual.fact.base] ?: return emptyList()
        return root.witnesses.keys.mapNotNull { profile ->
            cancellation?.checkpoint()
            if (markSub(profile, actual.fact.mark, catalog)) Cursor(root, profile) else null
        }
    }

    private inner class Cursor(private val node: Node<P>, private val profile: MarkSlot) : AnyDemandCursor {
        override fun follow(accessor: Int): AnyDemandCursor? {
            cancellation?.checkpoint()
            val child = node.child(accessor) ?: return null
            return if (profile in child.witnesses) Cursor(child, profile) else null
        }
        override fun subtreeWitness(): Pattern? = node.witnesses[profile]?.pattern
    }
}
