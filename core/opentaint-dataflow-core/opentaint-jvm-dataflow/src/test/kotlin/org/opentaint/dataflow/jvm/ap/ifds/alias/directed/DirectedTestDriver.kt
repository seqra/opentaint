package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import kotlin.test.assertEquals
import kotlin.test.assertNotNull

/**
 * The shared test driver of the directed engine. It does not use JIR. It builds an [AliasCfg]
 * with the direct builder, runs the fixpoint, and checks the post-fixpoint conditions of the
 * final states ([PostFixChecker], IMPL §9.1 item 3).
 *
 * The oracle tests ([LeanVectorTest], [NaiveConceptDifferentialTest], [ConcreteFuzzTest]) use it.
 * The other directed tests call [assertPostFix] on each solved program.
 *
 * @param symDepth K, the depth of the symbolic origins.
 * @param maxAccessors D, the depth of the query answers.
 */
class DirectedTestDriver(symDepth: Int = 7, val maxAccessors: Int = 6) {
    val tables = AliasTables(symDepth)
    val transfer = AliasTransfer(tables)
    val fixpoint = DirectedFixpoint(transfer)
    val nodes get() = tables.nodes
    val origins get() = tables.origins

    /** A CFG of the direct builder. */
    fun cfg(nodes: List<AliasCfg.Node>, entry: Int = 0): AliasCfg = AliasCfg.direct(tables, nodes, entry)

    /** Runs the fixpoint of [cfg] from [initial]. If [check] is true, the post-fixpoint check must pass. */
    fun solve(cfg: AliasCfg, initial: AliasState = AliasState.EMPTY, check: Boolean = true): FixpointStates {
        val states = fixpoint.solve(cfg, initial)
        if (check) assertPostFix(fixpoint, cfg, states, initial)
        return states
    }

    /** The violations of the post-fixpoint check. */
    fun violations(cfg: AliasCfg, states: FixpointStates, initial: AliasState = AliasState.EMPTY): List<String> =
        PostFixChecker(fixpoint).check(cfg, states, initial)

    /** Freezes the tables and gives the query of the result. Run it after all other uses of the tables. */
    fun query(cfg: AliasCfg, states: FixpointStates): AliasQuery {
        tables.freeze()
        return AliasQuery(DirectedAliasResult(tables, cfg, states.statesBefore, states.statesAfter), maxAccessors)
    }

    /** A state with the given values of locals: `env[v] := {o, ...}`. */
    fun stateWith(values: Map<VarId, IntArray>): AliasState {
        val ed = transfer.edit(AliasState.EMPTY)
        for ((v, os) in values) ed.setVar(v, nodes.of(*os))
        return ed.build()
    }

    /** The origins of the path `root.cells` in [st] (spec §5.2, default content by rule). Sorted. */
    fun pathValue(st: AliasState, root: AliasValue.Ref, cells: List<CellId>): IntArray {
        var n = transfer.valueNode(st, root)
        for (c in cells) n = transfer.load(st, n, c)
        return nodes.members(n)
    }

    /** May-alias of `x.px` and `y.py` in [st]: the two paths have a common origin. */
    fun may(st: AliasState, x: AliasValue.Ref, px: List<CellId>, y: AliasValue.Ref, py: List<CellId>): Boolean {
        val a = pathValue(st, x, px)
        val b = pathValue(st, y, py)
        var i = 0
        var j = 0
        while (i < a.size && j < b.size) {
            when {
                a[i] == b[j] -> return true
                a[i] < b[j] -> i++
                else -> j++
            }
        }
        return false
    }

    /**
     * Runs [instrs] as a straight-line CFG from [from] and checks the post-fixpoint conditions. The
     * last node reads each local of the table, so the kills keep each local. It gives the state
     * after the last instruction: the state of `instrs.fold(from, fixpoint::evaluate)`.
     */
    fun runStraight(fixpoint: DirectedFixpoint, instrs: List<AliasInstr>, from: AliasState): AliasState =
        runStraight(fixpoint, tables, instrs, from)

    companion object {
        /** See the member [runStraight]. [tables] are the tables of [fixpoint]. */
        fun runStraight(
            fixpoint: DirectedFixpoint,
            tables: AliasTables,
            instrs: List<AliasInstr>,
            from: AliasState,
        ): AliasState {
            val locals = (2 until tables.vars.size).toList().toIntArray()
            val nodes = instrs.mapIndexed { i, instr -> AliasCfg.Node(instr, intArrayOf(i + 1)) } +
                AliasCfg.Node(AliasInstr.Nop, extraUses = locals)
            val cfg = AliasCfg.direct(tables, nodes)
            val states = fixpoint.solve(cfg, from)
            assertPostFix(fixpoint, cfg, states, from)
            return assertNotNull(states.statesBefore[instrs.size], "no state after the instructions")
        }
    }
}

/** Checks the post-fixpoint conditions of [states] (IMPL §9.1 item 3) and fails with the violations. */
fun assertPostFix(
    fixpoint: DirectedFixpoint,
    cfg: AliasCfg,
    states: FixpointStates,
    initial: AliasState = AliasState.EMPTY,
) {
    assertEquals(emptyList(), PostFixChecker(fixpoint).check(cfg, states, initial), "post-fixpoint check")
}
