package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.graph.CompactGraph
import org.opentaint.dataflow.graph.MethodInstGraph
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.JIRPrimitiveType
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRCatchInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRLocalVar
import org.opentaint.ir.api.jvm.cfg.JIRValue
import org.opentaint.ir.api.jvm.cfg.values
import org.opentaint.jvm.graph.JApplicationGraph
import org.opentaint.util.analysis.ApplicationGraph

/**
 * The JIR builder of the alias CFG of [method] (IMPL §5.1).
 *
 * - Nodes: the instruction indices of `MethodInstGraph` (the same indices as main).
 * - Normal edges: the successors of `MethodInstGraph` without the edges into a `JIRCatchInst`.
 * - Exceptional edges: `t -> h` for each `t` in `h.throwers` (the raw JIR graph, not the cut graph
 *   of the taint analysis).
 * - Instructions: [lowering] of each JIR instruction.
 * - Liveness: the uses and the defs of each engine instruction, plus each reference local that the
 *   JIR instruction reads or writes. So a local that only a branch or a lowered-away operand reads
 *   is live at that statement, and a query there sees it.
 */
internal fun AliasCfg.Companion.build(
    tables: AliasTables,
    lowering: JIRAliasLowering,
    method: JIRMethod,
    entry: JIRInst,
    graph: JApplicationGraph,
    languageManager: JIRLanguageManager,
    context: Int = ROOT_CONTEXT,
    callOnCycle: Boolean = false,
): AliasCfg {
    @Suppress("UNCHECKED_CAST")
    val mig = MethodInstGraph.build(languageManager, graph as ApplicationGraph<CommonMethod, CommonInst>, method)
    return build(
        tables, lowering, mig.instructions.map { it as JIRInst }, mig.graph,
        languageManager.getInstIndex(entry), context, callOnCycle,
    )
}

/**
 * The alias CFG of a body with the instructions [statements] and the graph [graph] of
 * `MethodInstGraph` (the same indices), with the entry node [entryIndex]. The inlining builds a
 * callee body from the graph of the call resolution (`JIRInstGraph`).
 */
internal fun AliasCfg.Companion.build(
    tables: AliasTables,
    lowering: JIRAliasLowering,
    statements: List<JIRInst>,
    graph: CompactGraph,
    entryIndex: Int,
    context: Int,
    callOnCycle: Boolean,
): AliasCfg {
    val n = statements.size
    val insts = Array(n) { statements[it] }
    val isCatch = BooleanArray(n) { insts[it] is JIRCatchInst }

    val succ = Array(n) { v ->
        val out = IntArrayList()
        graph.forEachSuccessor(v) { w -> if (!isCatch[w]) out.add(w) }
        out.toIntArray()
    }

    val excLists = Array(n) { IntArrayList() }
    for (h in 0 until n) {
        val c = insts[h] as? JIRCatchInst ?: continue
        for (t in c.throwers) {
            val list = excLists[t.index]
            if (!list.contains(h)) list.add(h)
        }
    }
    val exc = Array(n) { excLists[it].toIntArray() }

    val instrs = Array(n) { lowering.lower(insts[it]) }
    val extraUses = Array(n) { jirReads(insts[it]).map { tables.vars.local(it.index, context) }.toIntArray() }
    val extraDefs = Array(n) { jirDef(insts[it])?.let { intArrayOf(tables.vars.local(it.index, context)) } ?: IntArray(0) }

    return AliasCfg.of(
        tables = tables,
        instrs = instrs,
        succ = succ,
        exc = exc,
        extraUses = extraUses,
        extraDefs = extraDefs,
        entry = entryIndex,
        context = context,
        callOnCycle = callOnCycle,
    )
}

/** The reference locals that [inst] reads. The local that an assignment writes is not a read. */
private fun jirReads(inst: JIRInst): List<JIRLocalVar> {
    val values: Collection<JIRValue> = when {
        inst is JIRCatchInst -> emptyList()
        inst is JIRAssignInst && inst.lhv is JIRLocalVar -> inst.rhv.values
        else -> inst.operands.flatMap { it.values }
    }
    return values.filterIsInstance<JIRLocalVar>().filter { it.type !is JIRPrimitiveType }.distinct()
}

/** The reference local that [inst] writes, or `null`. */
private fun jirDef(inst: JIRInst): JIRLocalVar? {
    val local = when (inst) {
        is JIRAssignInst -> inst.lhv as? JIRLocalVar
        is JIRCatchInst -> inst.throwable as? JIRLocalVar
        else -> null
    } ?: return null
    return local.takeIf { it.type !is JIRPrimitiveType }
}
