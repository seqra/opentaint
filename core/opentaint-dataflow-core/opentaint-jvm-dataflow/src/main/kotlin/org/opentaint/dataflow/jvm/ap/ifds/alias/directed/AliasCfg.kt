package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import java.util.BitSet

/**
 * A component of the weak topological order (WTO, Bourdoncle) of an [AliasCfg] (IMPL §5.2).
 * A [Loop] has a head and a body. The fixpoint iterates the body until the head is stable.
 */
sealed interface WtoComponent {
    data class Vertex(val node: Int) : WtoComponent

    data class Loop(val head: Int, val body: List<WtoComponent>) : WtoComponent
}

/**
 * The alias CFG of one method body (IMPL §5.1). It does not use JIR.
 *
 * - The nodes are the instruction indices `0 until size`. Node `v` has one engine instruction
 *   ([instr]).
 * - Normal edges ([successors]): the successors of `MethodInstGraph`, without the edges into a
 *   catch instruction.
 * - Exceptional edges ([handlers]): an edge `t -> h` for each thrower `t` of the handler `h`.
 * - [context]: the context of the locals of this body. The kill removes only these locals.
 *
 * The constructor computes the reachable nodes, the nodes on a cycle (both edge kinds), the WTO
 * (both edge kinds), and the live locals (IMPL §5.3). It marks the loop sites of the body in
 * [AliasTables.sites] (IMPL §5.4). So build the CFG before the fixpoint, before an `AllocNew`
 * origin of its sites exists.
 *
 * Make a CFG with [direct] (tests) or with the JIR builder (`AliasCfg.build`).
 */
class AliasCfg private constructor(
    private val tables: AliasTables,
    private val instrs: Array<AliasInstr>,
    private val succ: Array<IntArray>,
    private val exc: Array<IntArray>,
    private val uses: Array<IntArray>,
    private val defs: Array<IntArray>,
    val entry: Int,
    val context: Int,
    callOnCycle: Boolean,
) {
    /** A node of the direct builder. [extraUses] are reads of the source statement that [instr] does not have. */
    class Node(
        val instr: AliasInstr,
        val succ: IntArray = NO_NODES,
        val exc: IntArray = NO_NODES,
        val extraUses: IntArray = NO_NODES,
        val extraDefs: IntArray = NO_NODES,
    )

    val size: Int get() = instrs.size

    private val preds: Array<IntArray> = reverse(succ)
    private val excPreds: Array<IntArray> = reverse(exc)
    private val outs: Array<IntArray> = Array(size) { v -> (succ[v] + exc[v]).distinct().toIntArray() }

    private val reachable: BitSet = computeReachable()
    private val cyclic: BitSet = computeCycles()

    /** The WTO of the nodes that the entry reaches, both edge kinds included. */
    val wto: List<WtoComponent> = Wto().build()

    private val live: Array<BitSet> = computeLiveness()

    init {
        markLoopSites(callOnCycle)
    }

    fun instr(v: Int): AliasInstr = instrs[v]

    /** The normal successors of [v]. */
    fun successors(v: Int): IntArray = succ[v]

    /** The handlers of the thrower [v]: the targets of its exceptional edges. */
    fun handlers(v: Int): IntArray = exc[v]

    /** The normal predecessors of [v]. */
    fun normalPredecessors(v: Int): IntArray = preds[v]

    /** The throwers of the handler [h]: the sources of its exceptional edges. */
    fun throwers(h: Int): IntArray = excPreds[h]

    fun isReachable(v: Int): Boolean = reachable.get(v)

    /** True if [v] is on a cycle of the CFG (both edge kinds). */
    fun onCycle(v: Int): Boolean = cyclic.get(v)

    /** The locals that node [v] reads: the uses of its instruction and the extra uses. */
    fun uses(v: Int): IntArray = uses[v]

    /** The locals that node [v] writes: the defs of its instruction and the extra defs. */
    fun defs(v: Int): IntArray = defs[v]

    /** The locals that are live at the entry of [v] (IMPL §5.3). The caller must not change it. */
    fun liveIn(v: Int): BitSet = live[v]

    /** True if the kill at [v] keeps [x]: a reserved key, a local of another context, or a live local. */
    fun keepsAt(v: Int, x: VarId): Boolean {
        val key = tables.vars.key(x) ?: return true
        return key.context != context || live[v].get(x)
    }

    private fun computeReachable(): BitSet {
        val seen = BitSet(size)
        if (size == 0) return seen
        val work = IntArrayList()
        seen.set(entry)
        work.add(entry)
        while (!work.isEmpty) {
            val v = work.removeInt(work.size - 1)
            for (w in outs[v]) {
                if (!seen.get(w)) {
                    seen.set(w)
                    work.add(w)
                }
            }
        }
        return seen
    }

    private fun computeCycles(): BitSet {
        val all = BitSet(size).also { it.set(0, size) }
        val result = BitSet(size)
        val roots = if (size == 0) NO_NODES else intArrayOf(entry)
        for (scc in Tarjan().sccs(all, roots)) {
            if (scc.size > 1 || scc[0] in outs[scc[0]]) scc.forEach { result.set(it) }
        }
        return result
    }

    /**
     * The live locals: `live_in(v) = use(v) ∪ ⋃ normal successors w: (live_in(w) \ def(v)) ∪
     * ⋃ handlers h of v: live_in(h)`. An exception happens before the write of `v`, so a handler
     * keeps all its live locals at `v` (Lean `LiveOK`; `live_spec_unsound` for the rule without it).
     */
    private fun computeLiveness(): Array<BitSet> {
        val result = Array(size) { BitSet() }
        val queued = BitSet(size)
        val work = IntArrayList()
        for (v in size - 1 downTo 0) {
            work.add(v)
            queued.set(v)
        }
        while (!work.isEmpty) {
            val v = work.removeInt(work.size - 1)
            queued.clear(v)
            val out = BitSet()
            for (w in succ[v]) out.or(result[w])
            for (d in defs[v]) out.clear(d)
            for (u in uses[v]) out.set(u)
            for (h in exc[v]) out.or(result[h])
            if (out == result[v]) continue
            result[v] = out
            for (p in preds[v]) if (!queued.get(p)) { queued.set(p); work.add(p) }
            for (t in excPreds[v]) if (!queued.get(t)) { queued.set(t); work.add(t) }
        }
        return result
    }

    /**
     * Marks the loop sites (IMPL §5.4, Lean `onceB`). A site is a loop site if a node that has it is
     * on a cycle, or if more than one node has it. If [callOnCycle] is true (a callee body inlined
     * at a call on a cycle of the caller), each site of the body is a loop site.
     */
    private fun markLoopSites(callOnCycle: Boolean) {
        val count = mutableMapOf<SiteId, Int>()
        val loop = IntOpenHashSet()
        for (v in 0 until size) {
            val sites = IntOpenHashSet()
            instrs[v].forEachSite { sites.add(it) }
            val it = sites.iterator()
            while (it.hasNext()) {
                val s = it.nextInt()
                count[s] = (count[s] ?: 0) + 1
                if (callOnCycle || cyclic.get(v)) loop.add(s)
            }
        }
        for ((s, c) in count) if (c > 1) loop.add(s)
        val it = loop.iterator()
        while (it.hasNext()) tables.sites.markLoopSite(it.nextInt())
    }

    /**
     * Strongly connected components (Tarjan, iterative). [sccs] works on the subgraph of its
     * members. The DFS starts at the given roots, then at the other members in index order. The
     * result is in topological order. The first element of a component is its first visited node.
     * One instance serves many calls: each call resets the marks of its members.
     */
    private inner class Tarjan {
        private val index = IntArray(size) { -1 }
        private val low = IntArray(size)

        fun sccs(members: BitSet, roots: IntArray): List<IntArray> {
            val result = ArrayList<IntArray>()
            val onStack = BitSet(size)
            val stack = IntArrayList()
            val callNode = IntArrayList()
            val callPos = IntArrayList()
            var counter = 0

            fun start(v: Int) {
                index[v] = counter
                low[v] = counter
                counter++
                stack.add(v)
                onStack.set(v)
                callNode.add(v)
                callPos.add(0)
            }

            fun visit(r: Int) {
                if (!members.get(r) || index[r] != -1) return
                start(r)
                while (!callNode.isEmpty) {
                    val top = callNode.size - 1
                    val v = callNode.getInt(top)
                    val pos = callPos.getInt(top)
                    val vOuts = outs[v]
                    if (pos < vOuts.size) {
                        callPos.set(top, pos + 1)
                        val w = vOuts[pos]
                        if (!members.get(w)) continue
                        if (index[w] == -1) {
                            start(w)
                        } else if (onStack.get(w)) {
                            low[v] = minOf(low[v], index[w])
                        }
                        continue
                    }
                    callNode.removeInt(top)
                    callPos.removeInt(top)
                    if (low[v] == index[v]) {
                        val scc = IntArrayList()
                        scc.add(v)
                        while (true) {
                            val w = stack.removeInt(stack.size - 1)
                            onStack.clear(w)
                            if (w == v) break
                            scc.add(w)
                        }
                        result.add(scc.toIntArray())
                    }
                    if (!callNode.isEmpty) {
                        val u = callNode.getInt(callNode.size - 1)
                        low[u] = minOf(low[u], low[v])
                    }
                }
            }

            for (r in roots) visit(r)
            var m = members.nextSetBit(0)
            while (m >= 0) {
                visit(m)
                m = members.nextSetBit(m + 1)
            }
            // Reset for a later call on a subset of the members.
            m = members.nextSetBit(0)
            while (m >= 0) {
                index[m] = -1
                m = members.nextSetBit(m + 1)
            }
            result.reverse()
            return result
        }
    }

    /**
     * The WTO by recursive decomposition: the strongly connected components in topological order;
     * a component with a cycle is a [WtoComponent.Loop] whose head is its first visited node, and
     * its body is the decomposition of the component without the head. So each edge `u -> v` goes
     * forward in the order, or `v` is the head of a loop that contains `u`.
     */
    private inner class Wto {
        private val tarjan = Tarjan()

        fun build(): List<WtoComponent> {
            if (size == 0) return emptyList()
            return decompose(reachable, intArrayOf(entry))
        }

        private fun decompose(members: BitSet, roots: IntArray): List<WtoComponent> {
            val sccs = tarjan.sccs(members, roots)
            return sccs.map { scc ->
                val h = scc[0]
                if (scc.size == 1 && h !in outs[h]) {
                    WtoComponent.Vertex(h)
                } else {
                    val body = BitSet(size)
                    for (v in scc) body.set(v)
                    body.clear(h)
                    val bodyRoots = outs[h].filter { body.get(it) }.toIntArray()
                    WtoComponent.Loop(h, decompose(body, bodyRoots))
                }
            }
        }
    }

    companion object {
        private val NO_NODES = IntArray(0)

        /**
         * The direct builder (tests and later steps): node `v` is `nodes[v]`. The uses and the defs
         * of a node are the uses and the defs of its instruction, plus the extra ones.
         */
        fun direct(
            tables: AliasTables,
            nodes: List<Node>,
            entry: Int = 0,
            context: Int = ROOT_CONTEXT,
            callOnCycle: Boolean = false,
        ): AliasCfg = of(
            tables = tables,
            instrs = Array(nodes.size) { nodes[it].instr },
            succ = Array(nodes.size) { nodes[it].succ },
            exc = Array(nodes.size) { nodes[it].exc },
            extraUses = Array(nodes.size) { nodes[it].extraUses },
            extraDefs = Array(nodes.size) { nodes[it].extraDefs },
            entry = entry,
            context = context,
            callOnCycle = callOnCycle,
        )

        /**
         * A CFG with the given nodes. The uses and the defs of node `v` are the uses and the defs of
         * `instrs[v]`, plus `extraUses[v]` and `extraDefs[v]`.
         */
        internal fun of(
            tables: AliasTables,
            instrs: Array<AliasInstr>,
            succ: Array<IntArray>,
            exc: Array<IntArray>,
            extraUses: Array<IntArray>,
            extraDefs: Array<IntArray>,
            entry: Int,
            context: Int,
            callOnCycle: Boolean,
        ): AliasCfg = AliasCfg(
            tables = tables,
            instrs = instrs,
            succ = succ,
            exc = exc,
            uses = Array(instrs.size) { (instrs[it].uses() + extraUses[it]).distinct().toIntArray() },
            defs = Array(instrs.size) { (instrs[it].defs() + extraDefs[it]).distinct().toIntArray() },
            entry = entry,
            context = context,
            callOnCycle = callOnCycle,
        )

        private fun reverse(edges: Array<IntArray>): Array<IntArray> {
            val lists = Array(edges.size) { IntArrayList() }
            for (v in edges.indices) for (w in edges[v]) lists[w].add(v)
            return Array(edges.size) { lists[it].toIntArray() }
        }
    }
}

/** The locals that the instruction reads (Lean `Instr.uses`). */
fun AliasInstr.uses(): IntArray {
    val out = IntArrayList()
    fun add(v: AliasValue?) {
        if (v is AliasValue.Local) out.add(v.v)
    }
    when (this) {
        is AliasInstr.Assign -> add(value)
        is AliasInstr.StaticRead -> Unit
        is AliasInstr.FieldLoad -> add(base)
        is AliasInstr.ArrayLoad -> add(base)
        is AliasInstr.FieldStore -> { add(base); add(value) }
        is AliasInstr.ArrayStore -> { add(base); add(value) }
        AliasInstr.StaticWrite, AliasInstr.Nop -> Unit
        is AliasInstr.Return -> add(value)
        is AliasInstr.Throw -> add(value)
        is AliasInstr.UnresolvedCall -> args.forEach(::add)
        is AliasInstr.ResolvedCall -> args.forEach(::add)
    }
    return out.toIntArray()
}

/** The locals that the instruction writes (Lean `Instr.defs`). */
fun AliasInstr.defs(): IntArray = when (this) {
    is AliasInstr.Assign -> intArrayOf(dst)
    is AliasInstr.StaticRead -> intArrayOf(dst)
    is AliasInstr.FieldLoad -> intArrayOf(dst)
    is AliasInstr.ArrayLoad -> intArrayOf(dst)
    is AliasInstr.UnresolvedCall -> result?.let { intArrayOf(it) } ?: IntArray(0)
    is AliasInstr.ResolvedCall -> result?.let { intArrayOf(it) } ?: IntArray(0)
    else -> IntArray(0)
}

/** Calls [body] for each site of the instruction: the sites of its values and the call site. */
fun AliasInstr.forEachSite(body: (SiteId) -> Unit) {
    fun visit(v: AliasValue?) {
        when (v) {
            is AliasValue.New -> body(v.site)
            is AliasValue.Fresh -> body(v.site)
            is AliasValue.Box -> body(v.site)
            is AliasValue.Null -> body(v.site)
            else -> Unit
        }
    }
    when (this) {
        is AliasInstr.Assign -> visit(value)
        is AliasInstr.FieldStore -> visit(value)
        is AliasInstr.ArrayStore -> visit(value)
        is AliasInstr.Return -> visit(value)
        is AliasInstr.UnresolvedCall -> {
            body(site)
            args.forEach(::visit)
        }
        is AliasInstr.ResolvedCall -> {
            body(site)
            args.forEach(::visit)
        }
        else -> Unit
    }
}
