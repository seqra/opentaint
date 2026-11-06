package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

/**
 * The post-fixpoint checker (IMPL §9.1 item 3). A port of Lean `postFixB` (`Impl/CfgCheck.lean`)
 * with the engine order of `EPostFix` (`Impl/CfgEngine.lean`): `F ≤ E` if `E` is in normal form and
 * `join(E, F)` does not change `E`.
 *
 * The engine stores the state before a node after the kill of the node. So the kill of the target
 * node is on each edge. The conditions:
 * - entry: `kill(initial) ≤ statesBefore[entry]`;
 * - node `v`: `statesBefore[v]` has no dead local, is in normal form, and no written heap entry
 *   holds the empty set (A4; `EPostFix.ok`); `transfer(statesBefore[v]) ≤ statesAfter[v]`;
 * - normal edge `v -> w`: `kill_w(statesAfter[v]) ≤ statesBefore[w]`;
 * - exceptional edge `v -> h`: `kill_h(statesBefore[v]) ≤ statesBefore[h]`, and for a call also
 *   `kill_h(partial call of statesBefore[v]) ≤ statesBefore[h]` (Lean `partialS`).
 *
 * - liveness: the live sets of the kills are a liveness certificate with the handler rule (Lean
 *   `liveOKB`; the kill rule of `live_spec_unsound` fails it).
 *
 * Inlined calls (IMPL §5.5). The proof sees an inlined call as a spliced CFG: the callee nodes
 * replace the call node. The checker runs each override again from `statesBefore[c]` (the run is a
 * function of this state) and checks the spliced conditions:
 * - callee entry and callee nodes: the conditions above on the callee CFG, from `statesBefore[c]`;
 * - normal exit: each return state, with the result and without the callee variables, is below
 *   `statesAfter[c]` (the node condition of `c` with [DirectedFixpoint.inline]);
 * - exceptional exit: for each handler `h` of `c` and each callee node `t` (also the nodes of a
 *   nested inlined call), `kill_h(statesBefore[t])` and `kill_h(statesAfter[t])` without the callee
 *   variables are below `statesBefore[h]`. The partial call condition does not apply to `c`.
 *
 * These conditions give an `EPostFix` certificate of the CFG with kills at the node entries: the
 * certificate state before `w` is `statesBefore[w]` plus, for each local that `w` kills, the union
 * of its values on the edges into `w`. A pass is a soundness certificate for the method
 * (`postFixB_sound`, `csoundEngineCfg`).
 */
class PostFixChecker(private val fixpoint: DirectedFixpoint) {
    private val transfer = fixpoint.transfer
    private val origins = fixpoint.tables.origins

    /** The violations of the post-fixpoint conditions. An empty list is a pass. */
    fun check(cfg: AliasCfg, states: FixpointStates, initial: AliasState = AliasState.EMPTY): List<String> {
        val out = ArrayList<String>()
        check(cfg, states, initial, out)
        return out
    }

    private fun check(cfg: AliasCfg, states: FixpointStates, initial: AliasState, out: MutableList<String>) {
        val sb = states.statesBefore
        val sa = states.statesAfter

        val entryState = sb[cfg.entry]
        if (entryState == null) {
            out += "entry ${cfg.entry}: no state before"
        } else {
            le(out, fixpoint.kill(cfg, cfg.entry, initial), entryState, "entry ${cfg.entry}")
        }

        liveness(out, cfg)

        for (v in 0 until cfg.size) {
            val before = sb[v]
            val after = sa[v]
            if (before == null) {
                if (after != null) out += "node $v: a state after and no state before"
                continue
            }
            if (after == null) {
                out += "node $v: no state after"
                continue
            }
            normalForm(out, before, "node $v before")
            if (fixpoint.kill(cfg, v, before) != before) out += "node $v: a dead local in the state before"

            val instr = cfg.instr(v)
            val inlined = fixpoint.inline(cfg, v, before, exitNeeded = false)
            le(out, inlined?.after ?: fixpoint.evaluate(before, instr), after, "node $v")
            inlined?.runs?.forEachIndexed { i, run ->
                val sub = ArrayList<String>()
                check(run.cfg, run.states, before, sub)
                sub.mapTo(out) { "callee $i of node $v: $it" }
            }

            for (w in cfg.successors(v)) {
                val bw = sb[w]
                if (bw == null) {
                    out += "edge $v -> $w: no state before $w"
                    continue
                }
                le(out, fixpoint.kill(cfg, w, after), bw, "edge $v -> $w")
            }

            for (h in cfg.handlers(v)) {
                val bh = sb[h]
                if (bh == null) {
                    out += "exceptional edge $v -> $h: no state before $h"
                    continue
                }
                le(out, fixpoint.kill(cfg, h, before), bh, "exceptional edge $v -> $h")
                if (inlined != null) {
                    forEachSpliced(inlined) { st, where ->
                        le(out, fixpoint.kill(cfg, h, st), bh, "exceptional edge from $where of node $v -> $h")
                    }
                    continue
                }
                val partial = fixpoint.partialCall(before, instr) ?: continue
                le(out, fixpoint.kill(cfg, h, partial), bh, "exceptional edge $v -> $h (call)")
            }
        }
    }

    /**
     * Calls [body] for the states before and after each callee node of [inlined], without the
     * callee variables. A callee node that is an inlined call adds the nodes of its own callees
     * (the spliced CFG of a nested call).
     */
    private fun forEachSpliced(inlined: InlinedCall, body: (AliasState, String) -> Unit) {
        inlined.runs.forEachIndexed { i, run ->
            val ctx = run.cfg.context
            for (t in 0 until run.cfg.size) {
                val bt = run.states.statesBefore[t] ?: continue
                body(fixpoint.removeContext(bt, ctx), "callee $i node $t (before)")
                run.states.statesAfter[t]?.let { body(fixpoint.removeContext(it, ctx), "callee $i node $t (after)") }
                val nested = fixpoint.inline(run.cfg, t, bt, exitNeeded = false) ?: continue
                forEachSpliced(nested) { st, where -> body(fixpoint.removeContext(st, ctx), "callee $i node $t: $where") }
            }
        }
    }

    /**
     * The liveness certificate of the kills (Lean `liveOKB`, `kill_sim`, `csoundKill`): for each node
     * `v`, `use(v) ⊆ live(v)`, `live(w) \ def(v) ⊆ live(v)` for each normal successor `w`, and
     * `live(h) ⊆ live(v)` for each handler `h`. The kill at `v` removes only locals that are not in
     * `live(v)`, so with this condition each kill is sound.
     */
    private fun liveness(out: MutableList<String>, cfg: AliasCfg) {
        for (v in 0 until cfg.size) {
            val live = cfg.liveIn(v)
            for (u in cfg.uses(v)) if (!live.get(u)) out += "liveness at $v: the read local $u is not live"
            val defs = cfg.defs(v)
            for (w in cfg.successors(v)) {
                val lw = cfg.liveIn(w)
                var x = lw.nextSetBit(0)
                while (x >= 0) {
                    if (!live.get(x) && x !in defs) out += "liveness at $v: local $x of successor $w is not live"
                    x = lw.nextSetBit(x + 1)
                }
            }
            for (h in cfg.handlers(v)) {
                val lh = cfg.liveIn(h)
                var x = lh.nextSetBit(0)
                while (x >= 0) {
                    if (!live.get(x)) out += "liveness at $v: local $x of handler $h is not live"
                    x = lh.nextSetBit(x + 1)
                }
            }
        }
    }

    /** `f ≤ e`: `e` is in normal form and the join does not change it. */
    private fun le(out: MutableList<String>, f: AliasState, e: AliasState, where: String) {
        normalForm(out, e, where)
        if (transfer.join(e, f).changed) out += "$where: the state is not below the target state"
    }

    private fun normalForm(out: MutableList<String>, st: AliasState, where: String) {
        st.forEachVar { v, n ->
            if (n == EMPTY_NODE) out += "$where: env entry $v holds the empty node"
        }
        st.forEachHeap { key, n ->
            val o = heapKeyOrigin(key)
            val c = heapKeyCell(key)
            if (n == EMPTY_NODE) out += "$where: heap entry ($o, $c) holds the empty set"
            if (n == origins.defaultNode(o, c)) out += "$where: heap entry ($o, $c) holds its default node"
        }
    }
}
