package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisCancellation

/**
 * The states of one fixpoint run: the state before and the state after each node of the CFG.
 * A node that the run does not reach has no state (`null`).
 *
 * [exits]: for an inlined call node, the state on its exceptional exit (IMPL §5.5 step 3): the join
 * of the states before and after each callee node, without the callee variables. It is `null` for
 * another node, and for a call whose exit no handler reads.
 */
class FixpointStates(
    val statesBefore: Array<AliasState?>,
    val statesAfter: Array<AliasState?>,
    val exits: Array<AliasState?> = arrayOfNulls(statesBefore.size),
)

/**
 * The evaluation of an inlined call (IMPL §5.5).
 *
 * - [after]: the state after the call: the join over the return states of all overrides, or the
 *   rule of the unresolved call if no override gives a return state. If an override has no body
 *   ([CalleeBodies.hasBodilessOverride]), the join also has the rule of the unresolved call.
 * - [exit]: the state on the exceptional exit (step 3), or `null` if it was not asked for.
 * - [runs]: the fixpoint run of each override (the post-fixpoint checker reads them).
 */
class InlinedCall(
    val after: AliasState,
    val exit: AliasState?,
    val runs: List<CalleeRun>,
)

/** The fixpoint run of one inlined body [cfg] from the state before the call. */
class CalleeRun(val cfg: AliasCfg, val states: FixpointStates)

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
 * - catch handler `h`: the join of `statesBefore[t]` and `statesAfter[t]` of each thrower `t`, and,
 *   for an inlined call `t`, the state on its exceptional exit (IMPL §5.5 step 3);
 * - loop head: the join of the accumulated head state and the inputs;
 * - other: the join of `statesAfter` of the predecessors.
 * Then the kill removes the dead locals of the current context ([AliasCfg.keepsAt]). An input that
 * is not computed yet is no state (`null`), never [AliasState.EMPTY].
 *
 * Calls: an unresolved call is the passive call of IMPL §4.4 with the pass-through models of
 * IMPL §4.5 ([AliasCall]). A resolved call with bodies is inlined ([inline], IMPL §5.5). A resolved
 * call without a body uses the rule of the unresolved call with its models.
 *
 * [maxCallClosure]: the budget of the call closure (`JIRLocalAliasAnalysis.Params.maxCallClosure`).
 */
class DirectedFixpoint(
    val transfer: AliasTransfer,
    private val cancellation: AnalysisCancellation? = null,
    maxCallClosure: Int = DEFAULT_MAX_CALL_CLOSURE,
) {
    val tables: AliasTables get() = transfer.tables

    /** The transfer of the calls. */
    val calls = AliasCall(transfer, maxCallClosure)

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
    fun solve(cfg: AliasCfg, initial: AliasState = AliasState.EMPTY): FixpointStates =
        solve(cfg, initial, exitNeeded = false)

    /**
     * Runs the fixpoint of [cfg] from [initial]. If [exitNeeded] is true, the run computes the
     * exceptional exit of each inlined call ([FixpointStates.exits]): a body inlined at a call whose
     * exit a handler reads.
     */
    private fun solve(cfg: AliasCfg, initial: AliasState, exitNeeded: Boolean): FixpointStates {
        val run = Run(cfg, initial, exitNeeded)
        for (c in cfg.wto) run.stabilize(c)
        return FixpointStates(run.before, run.after, run.exits)
    }

    /**
     * The inlining of the resolved call at node [v] of [cfg] from the state [st] before it
     * (IMPL §5.5). It is `null` if the node is not a resolved call with bodies ([AliasCfg.callees]).
     *
     * 1. Each override runs on its own CFG with new state arrays, from [st]. The callee locals have
     *    the callee context. The callee `this` and arguments are the values of the call (the
     *    lowering puts them into the callee instructions).
     * 2. Normal exit: for each `Return(value)` with a state after it: `env[result] := value(value)`,
     *    then the callee variables are removed. The state after the call is the join over all
     *    returns of all overrides. With no return state, the call uses the rule of the unresolved
     *    call with its models.
     * 3. Exceptional exit (if [exitNeeded]): the join of the states before and after each callee
     *    node, and of the exceptional exit of each inlined call in the callee, without the callee
     *    variables. Each callee node is a thrower of the caller handlers of the call.
     * 4. An unresolved call in a callee is a passive call on the shared state: it grows `Etree` and
     *    `Eval`, and these keys stay after the return.
     *
     * An override without a body ([CalleeBodies.hasBodilessOverride]: a native method, for example)
     * is an unresolved call: the state after the call also joins the rule of the unresolved call
     * with the models, and the exceptional exit also joins the partial call ([partialCall]).
     */
    fun inline(cfg: AliasCfg, v: Int, st: AliasState, exitNeeded: Boolean): InlinedCall? {
        val call = cfg.instr(v) as? AliasInstr.ResolvedCall ?: return null
        val callees = cfg.callees(v)
        if (callees.isEmpty()) return null
        var returned: AliasState? = null
        var exit: AliasState? = null
        val runs = ArrayList<CalleeRun>(callees.size)
        for (callee in callees) {
            val states = solve(callee, st, exitNeeded)
            runs += CalleeRun(callee, states)
            for (r in 0 until callee.size) {
                val ret = callee.instr(r) as? AliasInstr.Return ?: continue
                val a = states.statesAfter[r] ?: continue
                returned = join(returned, returnState(a, ret, call.result, callee.context))
            }
            if (exitNeeded) {
                var calleeExit: AliasState? = null
                for (t in 0 until callee.size) {
                    calleeExit = join(calleeExit, states.statesBefore[t])
                    calleeExit = join(calleeExit, states.statesAfter[t])
                    calleeExit = join(calleeExit, states.exits[t])
                }
                exit = join(exit, calleeExit?.let { removeContext(it, callee.context) })
            }
        }
        val bodiless = call.callees.hasBodilessOverride
        val after = if (bodiless) join(returned, evaluate(st, call))!! else returned ?: evaluate(st, call)
        if (exitNeeded && bodiless) exit = join(exit, partialCall(st, call))
        tables.counters.inlinedCalls++
        return InlinedCall(after, exit, runs)
    }

    /** IMPL §5.5 step 2: the state after `return value` of a callee with [context], for the call result [result]. */
    private fun returnState(st: AliasState, ret: AliasInstr.Return, result: VarId?, context: Int): AliasState {
        var cur = st
        if (result != null) {
            val value = ret.value
            val ed: AliasState.Editor
            if (value == null) {
                ed = transfer.edit(cur)
                ed.removeVar(result)
            } else {
                val (s, n) = transfer.evaluate(cur, value)
                ed = transfer.edit(s)
                ed.setVar(result, n)
            }
            cur = ed.build()
        }
        return removeContext(cur, context)
    }

    /** Removes the locals of [context]. The reserved keys stay. */
    fun removeContext(st: AliasState, context: Int): AliasState =
        transfer.kill(st) { tables.vars.key(it)?.context != context }

    private fun join(a: AliasState?, b: AliasState?): AliasState? = when {
        a == null -> b
        b == null -> a
        else -> transfer.join(a, b).state
    }

    /**
     * The state after [instr] from the state [st] before it. A resolved call uses the rule of the
     * unresolved call here; [inline] gives the state after an inlined call.
     */
    fun evaluate(st: AliasState, instr: AliasInstr): AliasState = when (instr) {
        is AliasInstr.UnresolvedCall -> calls.unresolved(st, instr.site, instr.result, instr.args, instr.models)
        is AliasInstr.ResolvedCall -> calls.unresolved(st, instr.site, instr.result, instr.args, instr.models)
        else -> transfer.transfer(st, instr)
    }

    /**
     * The state on an exceptional edge of a call: the passive call without its result and without
     * the models (Lean `partialS`). It is `null` for an instruction that is not a call. The
     * exceptional exit of an inlined call is the exit of its callee nodes instead ([inline]).
     */
    fun partialCall(st: AliasState, instr: AliasInstr): AliasState? = when (instr) {
        is AliasInstr.UnresolvedCall -> calls.call(st, calls.roots(st, instr.args))
        is AliasInstr.ResolvedCall -> calls.call(st, calls.roots(st, instr.args))
        else -> null
    }

    /** The kill at node [v]: removes the dead locals of the current context (IMPL §5.3). */
    fun kill(cfg: AliasCfg, v: Int, st: AliasState): AliasState = transfer.kill(st) { cfg.keepsAt(v, it) }

    /**
     * One fixpoint run of [cfg] from [initial]. [exitNeeded]: the body is inlined at a call whose
     * exceptional exit a handler reads, so each inlined call of the body computes its exit.
     */
    private inner class Run(
        private val cfg: AliasCfg,
        private val initial: AliasState,
        private val exitNeeded: Boolean,
    ) {
        val before = arrayOfNulls<AliasState>(cfg.size)
        val after = arrayOfNulls<AliasState>(cfg.size)
        val exits = arrayOfNulls<AliasState>(cfg.size)

        /** The join of the inputs of [v] after the kill, or `null` if no input is computed. */
        private fun inputs(v: Int): AliasState? {
            var acc: AliasState? = if (v == cfg.entry) initial else null
            for (p in cfg.normalPredecessors(v)) acc = join(acc, after[p])
            for (t in cfg.throwers(v)) {
                acc = join(acc, before[t])
                acc = join(acc, after[t])
                acc = join(acc, exits[t])
            }
            return acc?.let { kill(cfg, v, it) }
        }

        private fun evalNode(v: Int, st: AliasState) {
            cancellation?.checkpoint()
            tables.counters.stmtEvals++
            before[v] = st
            val inlined = inline(cfg, v, st, exitNeeded || cfg.handlers(v).isNotEmpty())
            if (inlined != null) {
                after[v] = inlined.after
                exits[v] = inlined.exit
            } else {
                after[v] = evaluate(st, cfg.instr(v))
            }
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
                    var iterations = 0L
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
                        iterations++
                        acc = next
                        if (acc != null) evalNode(h, acc)
                        for (b in c.body) stabilize(b)
                    }
                    tables.counters.recordHeadIterations(iterations)
                }
            }
        }
    }
}
