package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisCancellation

/**
 * The states of one fixpoint run: the state before and the state after each node of the CFG.
 * A node that the run does not reach has no state (`null`).
 */
class FixpointStates(
    val statesBefore: Array<AliasState?>,
    val statesAfter: Array<AliasState?>,
)

/**
 * The result of the directed analysis of one method (IMPL §2): the frozen tables, the alias CFG,
 * and the state before and after each statement (`null`: not reached).
 */
class DirectedAliasResult(
    val tables: AliasTables,
    val cfg: AliasCfg,
    val statesBefore: Array<AliasState?>,
    val statesAfter: Array<AliasState?>,
)

/**
 * The WTO fixpoint over an [AliasCfg] (IMPL §5.1, §5.2; spec §5.5).
 *
 * State before a node:
 * - entry: the join of the initial state and the inputs of the predecessors;
 * - catch handler `h`: the join of `statesBefore[t]` and `statesAfter[t]` of each thrower `t`;
 * - loop head: the join of the accumulated head state and the inputs;
 * - other: the join of `statesAfter` of the predecessors.
 * Then the kill removes the dead locals of the current context ([AliasCfg.keepsAt]). An input that
 * is not computed yet is no state (`null`), never [AliasState.EMPTY].
 *
 * Calls: this step has no call closure (IMPL §4.4, step T4) and no inlining (IMPL §5.5, step T6).
 * A call, resolved or not, is the provisional unresolved call [provisionalCall].
 */
class DirectedFixpoint(
    val transfer: AliasTransfer,
    private val cancellation: AnalysisCancellation? = null,
) {
    val tables: AliasTables get() = transfer.tables

    private val nodes = tables.nodes
    private val reachedAll: NodeId by lazy { nodes.singleton(OriginTable.REACHED_ALL) }

    /**
     * Runs the fixpoint of [cfg] from the entry state. If [verify] is true, it checks the
     * post-fixpoint conditions ([PostFixChecker]) and fails on a violation. Then it freezes the tables.
     */
    fun run(cfg: AliasCfg, verify: Boolean = false): DirectedAliasResult {
        val states = solve(cfg)
        if (verify) {
            val violations = PostFixChecker(this).check(cfg, states)
            check(violations.isEmpty()) { "Post-fixpoint check failed:\n" + violations.joinToString("\n") }
        }
        tables.freeze()
        return DirectedAliasResult(tables, cfg, states.statesBefore, states.statesAfter)
    }

    /** Runs the fixpoint of [cfg] from [initial]. It does not freeze the tables. */
    fun solve(cfg: AliasCfg, initial: AliasState = AliasState.EMPTY): FixpointStates {
        val run = Run(cfg, initial)
        for (c in cfg.wto) run.stabilize(c)
        return FixpointStates(run.before, run.after)
    }

    /** The state after [instr] from the state [st] before it. */
    fun evaluate(st: AliasState, instr: AliasInstr): AliasState = when (instr) {
        is AliasInstr.UnresolvedCall -> provisionalCall(st, instr.site, instr.result)
        is AliasInstr.ResolvedCall -> provisionalCall(st, instr.site, instr.result)
        else -> transfer.transfer(st, instr)
    }

    /**
     * The state on an exceptional edge of a call: the call without its result (Lean `partialS`).
     * It is `null` for an instruction that is not a call.
     */
    fun partialCall(st: AliasState, instr: AliasInstr): AliasState? = when (instr) {
        is AliasInstr.UnresolvedCall -> provisionalCall(st, instr.site, null)
        is AliasInstr.ResolvedCall -> provisionalCall(st, instr.site, null)
        else -> null
    }

    /**
     * The provisional call of this step: `Etree` and `Eval` get [OriginTable.REACHED_ALL] (the sound
     * fallback of IMPL §4.4: no origin is unique after the call), and the result gets
     * `{Sym(FRESH(site))}`. The call writes no heap entry. The call closure (step T4) replaces it.
     */
    fun provisionalCall(st: AliasState, site: SiteId, result: VarId?): AliasState {
        val ed = transfer.edit(st)
        ed.setVar(ETREE, nodes.union(st.varNode(ETREE), reachedAll))
        ed.setVar(EVAL, nodes.union(st.varNode(EVAL), reachedAll))
        if (result != null) ed.setVar(result, transfer.evaluate(st, AliasValue.Fresh(site)).node)
        return ed.build()
    }

    /** The kill at node [v]: removes the dead locals of the current context (IMPL §5.3). */
    fun kill(cfg: AliasCfg, v: Int, st: AliasState): AliasState = transfer.kill(st) { cfg.keepsAt(v, it) }

    private inner class Run(private val cfg: AliasCfg, private val initial: AliasState) {
        val before = arrayOfNulls<AliasState>(cfg.size)
        val after = arrayOfNulls<AliasState>(cfg.size)

        /** The join of the inputs of [v] after the kill, or `null` if no input is computed. */
        private fun inputs(v: Int): AliasState? {
            var acc: AliasState? = if (v == cfg.entry) initial else null
            for (p in cfg.normalPredecessors(v)) acc = join(acc, after[p])
            for (t in cfg.throwers(v)) {
                acc = join(acc, before[t])
                acc = join(acc, after[t])
            }
            return acc?.let { kill(cfg, v, it) }
        }

        private fun join(a: AliasState?, b: AliasState?): AliasState? = when {
            a == null -> b
            b == null -> a
            else -> transfer.join(a, b).state
        }

        private fun evalNode(v: Int, st: AliasState) {
            cancellation?.checkpoint()
            before[v] = st
            after[v] = evaluate(st, cfg.instr(v))
        }

        /**
         * IMPL §5.2. A loop has a new accumulator for each run, so an inner loop restarts at each
         * iteration of its outer loop. The head state only grows. The body runs at least once, also
         * if the head has no input yet (a cycle of an irreducible CFG can have its entry in the body).
         */
        fun stabilize(c: WtoComponent) {
            when (c) {
                is WtoComponent.Vertex -> {
                    val st = inputs(c.node) ?: return
                    evalNode(c.node, st)
                }

                is WtoComponent.Loop -> {
                    val h = c.head
                    var acc: AliasState? = null
                    var first = true
                    while (true) {
                        val input = inputs(h)
                        val next: AliasState?
                        val changed: Boolean
                        when {
                            acc == null -> {
                                next = input
                                changed = input != null
                            }

                            input == null -> {
                                next = acc
                                changed = false
                            }

                            else -> {
                                val joined = transfer.join(acc, input)
                                next = joined.state
                                changed = joined.changed
                            }
                        }
                        if (!first && !changed) break
                        first = false
                        acc = next
                        if (acc != null) evalNode(h, acc)
                        for (b in c.body) stabilize(b)
                    }
                }
            }
        }
    }
}
