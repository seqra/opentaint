package org.opentaint.dataflow.go.analysis.alias

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAHeapAccessor
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfoManager
import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisCancellation
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.HeapAlias
import org.opentaint.dataflow.ap.ifds.analysis.alias.ImmutableState
import org.opentaint.dataflow.ap.ifds.analysis.alias.IntDisjointSets
import org.opentaint.dataflow.ap.ifds.analysis.alias.State
import org.opentaint.dataflow.ap.ifds.analysis.alias.allElements
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.graph.simulateGraph
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.cfg.GoIRCallInfo
import org.opentaint.ir.go.cfg.GoIRCallTarget
import org.opentaint.ir.go.expr.GoIRAllocExpr
import org.opentaint.ir.go.expr.GoIRChangeInterfaceExpr
import org.opentaint.ir.go.expr.GoIRChangeTypeExpr
import org.opentaint.ir.go.expr.GoIRConvertExpr
import org.opentaint.ir.go.expr.GoIRExpr
import org.opentaint.ir.go.expr.GoIRExtractExpr
import org.opentaint.ir.go.expr.GoIRFieldAddrExpr
import org.opentaint.ir.go.expr.GoIRFieldExpr
import org.opentaint.ir.go.expr.GoIRFreeVarValueExpr
import org.opentaint.ir.go.expr.GoIRGlobalValueExpr
import org.opentaint.ir.go.expr.GoIRIndexAddrExpr
import org.opentaint.ir.go.expr.GoIRIndexExpr
import org.opentaint.ir.go.expr.GoIRLookupExpr
import org.opentaint.ir.go.expr.GoIRMakeChanExpr
import org.opentaint.ir.go.expr.GoIRMakeClosureExpr
import org.opentaint.ir.go.expr.GoIRMakeInterfaceExpr
import org.opentaint.ir.go.expr.GoIRMakeMapExpr
import org.opentaint.ir.go.expr.GoIRMakeSliceExpr
import org.opentaint.ir.go.expr.GoIRNextExpr
import org.opentaint.ir.go.expr.GoIRRangeExpr
import org.opentaint.ir.go.expr.GoIRSliceExpr
import org.opentaint.ir.go.expr.GoIRUnOpExpr
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRCall
import org.opentaint.ir.go.inst.GoIRFieldStore
import org.opentaint.ir.go.inst.GoIRGlobalStore
import org.opentaint.ir.go.inst.GoIRIndexStore
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.inst.GoIRMapUpdate
import org.opentaint.ir.go.inst.GoIRPhi
import org.opentaint.ir.go.inst.GoIRReturn
import org.opentaint.ir.go.inst.GoIRSend
import org.opentaint.ir.go.inst.GoIRStore
import org.opentaint.ir.go.inst.GoIRStoreInst
import org.opentaint.ir.go.type.GoIRCallMode
import org.opentaint.ir.go.type.GoIRUnaryOp
import org.opentaint.ir.go.value.GoIRParameterValue
import org.opentaint.ir.go.value.GoIRRegister
import org.opentaint.ir.go.value.GoIRValue

class GoDSUAliasAnalysis(
    private val rootFunction: GoIRFunction,
    private val interProcCallDepth: Int,
    val cancellation: AnalysisCancellation
) {
    val aliasManager = AAInfoManager()
    val dsuMergeStrategy = DsuMergeStrategy(aliasManager)

    class DsuMergeStrategy(private val manager: AAInfoManager) : IntDisjointSets.RankStrategy {
        override fun compare(a: Int, b: Int): Int =
            manager.getElementUncheck(a).compareTo(manager.getElementUncheck(b))
    }

    data class ConnectedAliases(val aliasGroups: Int2ObjectOpenHashMap<List<AAInfo>>)

    class AnalysisResult(
        val manager: AAInfoManager,
        val statesBeforeStmt: Array<ImmutableState?>,
        val statesAfterStmt: Array<ImmutableState?>,
    )

    class GraphAnalysisState(size: Int, val ctx: ContextInfo, val function: GoIRFunction) {
        val stateBeforeStmt = arrayOfNulls<ImmutableState>(size)
        val stateAfterStmt = arrayOfNulls<ImmutableState>(size)
    }

    private data class AliasSet(val repr: Int)

    private val graphCache = HashMap<GoIRFunction, GoInstGraph?>()
    private val closureAllocFns = HashMap<GoLocalAlias.Alloc, GoIRFunction>()
    private val calleeArgMap = HashMap<ContextInfo, List<GoRefValue?>>()
    private val calleeClosure = HashMap<ContextInfo, GoRefValue?>()

    fun analyze(): AnalysisResult {
        val rootGraph = GoCompactGraphBuilder.build(rootFunction)
            ?: return AnalysisResult(aliasManager, emptyArray(), emptyArray())
        graphCache[rootFunction] = rootGraph
        val initial = State.empty(aliasManager, dsuMergeStrategy)
        val gas = GraphAnalysisState(rootGraph.statements.size, ContextInfo.rootContext, rootFunction)
        val (before, after) = analyze(rootGraph, initial, gas)
        return AnalysisResult(aliasManager, before, after)
    }

    private fun analyze(
        jig: GoInstGraph,
        initialState: ImmutableState,
        gas: GraphAnalysisState,
    ): Pair<Array<ImmutableState?>, Array<ImmutableState?>> {
        val before = gas.stateBeforeStmt
        val after = gas.stateAfterStmt
        simulateGraph<ImmutableState>(
            statesAfter = after,
            graph = jig.graph,
            initialStmtIdx = jig.initialIdx,
            initialState = initialState,
            merge = { _, states -> State.merge(aliasManager, dsuMergeStrategy, states.values.filterNotNull()) },
            eval = { idx, st ->
                cancellation.checkpoint()

                before[idx] = st
                step(jig.statements[idx], st, gas)
            },
        )
        return before to after
    }

    private fun step(inst: GoIRInst, stateBefore: ImmutableState, gas: GraphAnalysisState): ImmutableState {
        val s = stateBefore.mutableCopy()
        return evalMutable(inst, s, gas).asImmutable()
    }

    private fun evalMutable(inst: GoIRInst, state: State, gas: GraphAnalysisState): State {
        val ctx = gas.ctx
        return when (inst) {
            is GoIRAssignInst -> evalAssign(inst, state, gas)
            is GoIRStoreInst -> when (inst) {
                is GoIRFieldStore -> evalFieldStore(inst, state, ctx)
                is GoIRIndexStore -> evalIndexStore(inst, state, ctx)
                is GoIRStore -> evalStore(inst, state, ctx)
            }
            is GoIRGlobalStore -> evalGlobalStore(inst, state, ctx)
            is GoIRMapUpdate -> evalContainerStore(inst.map, inst.value, state, ctx)
            is GoIRSend -> evalContainerStore(inst.chan, inst.x, state, ctx)
            is GoIRPhi -> evalPhi(inst, state, ctx)
            is GoIRCall -> evalCall(inst, state, gas)
            is GoIRReturn -> state
            else -> state
        }
    }

    private fun evalAssign(inst: GoIRAssignInst, state: State, gas: GraphAnalysisState): State {
        val ctx = gas.ctx
        val lhs = registerLocal(inst.register, ctx)
        return when (val expr = inst.expr) {
            is GoIRMakeClosureExpr -> evalMakeClosure(inst, expr, state, gas)
            is GoIRFieldAddrExpr ->
                evalAddrLink(lhs, refValueOf(expr.x, ctx), GoFieldAlias(structFieldAccessor(expr.x, expr.fieldName)), state)
            is GoIRIndexAddrExpr ->
                evalAddrLink(lhs, refValueOf(expr.x, ctx), GoArrayAlias, state)
            else -> state.removeOldAndMergeWith(lhs.aliasInfo().index(), evalExpr(expr, inst, state, gas))
        }
    }

    private fun evalAddrLink(
        lhs: GoRefValue.Local,
        instance: GoRefValue?,
        accessor: AAHeapAccessor,
        state: State,
    ): State {
        val s = state.remove(lhs.aliasInfo().index())
        if (instance == null) return s
        val tRef = HeapAlias(s.heapObj(lhs.aliasInfo()), GoRefAlias).index()
        val target = HeapAlias(s.heapObj(instance.aliasInfo()), accessor).index()
        return s.mergeWith(tRef, target)
    }

    private fun evalExpr(expr: GoIRExpr, inst: GoIRInst, state: State, gas: GraphAnalysisState): AliasSet {
        val ctx = gas.ctx
        val instIdx = inst.location.index
        return when (expr) {
            is GoIRAllocExpr, is GoIRMakeMapExpr, is GoIRMakeSliceExpr, is GoIRMakeChanExpr ->
                aliasSetFromInfo(GoLocalAlias.Alloc(instIdx, ctx))

            is GoIRFieldExpr ->
                heapLoad(refValueOf(expr.x, ctx), state, instIdx, ctx, GoFieldAlias(structFieldAccessor(expr.x, expr.fieldName)))

            is GoIRIndexExpr -> heapLoad(refValueOf(expr.x, ctx), state, instIdx, ctx, GoArrayAlias)
            is GoIRLookupExpr -> heapLoad(refValueOf(expr.x, ctx), state, instIdx, ctx, GoArrayAlias)
            is GoIRNextExpr -> heapLoad(refValueOf(expr.iter, ctx), state, instIdx, ctx, GoArrayAlias)

            is GoIRUnOpExpr -> when (expr.op) {
                GoIRUnaryOp.DEREF -> heapLoad(refValueOf(expr.x, ctx), state, instIdx, ctx, GoRefAlias)
                GoIRUnaryOp.ARROW -> heapLoad(refValueOf(expr.x, ctx), state, instIdx, ctx, GoArrayAlias)
                else -> unknown(instIdx, ctx)
            }

            is GoIRGlobalValueExpr -> aliasSetFromInfo(GoLocalAlias.SimpleLoc(GoRefValue.Global(expr.global.fullName)))

            is GoIRFreeVarValueExpr -> {
                val closure = freeVarValue(ctx)
                aliasSetFromInfo(HeapAlias(state.heapObj(closure.aliasInfo()), GoFieldAlias(freeVarField(gas.function, expr.freeVarIndex))))
            }

            is GoIRExtractExpr -> copyOf(expr.tuple, state, instIdx, ctx)
            is GoIRConvertExpr -> copyOf(expr.x, state, instIdx, ctx)
            is GoIRChangeTypeExpr -> copyOf(expr.x, state, instIdx, ctx)
            is GoIRChangeInterfaceExpr -> copyOf(expr.x, state, instIdx, ctx)
            is GoIRMakeInterfaceExpr -> copyOf(expr.x, state, instIdx, ctx)
            is GoIRSliceExpr -> copyOf(expr.x, state, instIdx, ctx)
            is GoIRRangeExpr -> copyOf(expr.x, state, instIdx, ctx)

            else -> unknown(instIdx, ctx)
        }
    }

    private fun copyOf(value: GoIRValue, state: State, instIdx: Int, ctx: ContextInfo): AliasSet {
        val rv = refValueOf(value, ctx) ?: return unknown(instIdx, ctx)
        return aliasSetFromInfo(rv.aliasInfo())
    }

    private fun heapLoad(
        instance: GoRefValue?,
        state: State,
        instIdx: Int,
        ctx: ContextInfo,
        accessor: AAHeapAccessor,
    ): AliasSet {
        if (instance == null) return unknown(instIdx, ctx)
        return aliasSetFromInfo(HeapAlias(state.heapObj(instance.aliasInfo()), accessor))
    }

    private fun evalFieldStore(inst: GoIRFieldStore, state: State, ctx: ContextInfo): State {
        // todo: simplify impl
        return evalStore(inst.toGenericStore(), state, ctx)
    }

    private fun evalIndexStore(inst: GoIRIndexStore, state: State, ctx: ContextInfo): State {
        // todo: simplify impl
        return evalStore(inst.toGenericStore(), state, ctx)
    }

    private fun evalStore(inst: GoIRStore, state: State, ctx: ContextInfo): State {
        val addr = refValueOf(inst.addr, ctx) ?: return state
        val valueSet = refValueOf(inst.value, ctx)?.let { aliasSetFromInfo(it.aliasInfo()) }
            ?: unknown(inst.location.index, ctx)
        val refLoc = HeapAlias(state.heapObj(addr.aliasInfo()), GoRefAlias).index()

        val locationNodes = IntOpenHashSet()
        val instances = IntOpenHashSet()
        var weak = false
        state.forEachAliasInSet(refLoc) { id ->
            val info = aliasManager.getElementUncheck(id)
            if (info is HeapAlias) {
                locationNodes.add(id)
                if (info.heapAccessor is GoArrayAlias) weak = true
                if (info.heapAccessor !is GoRefAlias) instances.add(info.instance)
            }
        }
        locationNodes.add(refLoc)

        val instanceForCheck = if (instances.size == 1) instances.iterator().nextInt() else addr.aliasInfo().index()
        if (weak || instances.size > 1 ||
            state.containsMultipleConcreteOrOuterLocations(instanceForCheck, IntOpenHashSet())
        ) {
            return state.mergeWith(refLoc, valueSet.repr)
        }

        val s = state.removeUnsafe(locationNodes)
        val merged = IntOpenHashSet(locationNodes)
        merged.add(valueSet.repr)
        return s.mergeAliasSets(merged)
    }

    private fun evalGlobalStore(inst: GoIRGlobalStore, state: State, ctx: ContextInfo): State {
        val global = GoRefValue.Global(inst.global.fullName)
        val valueSet = refValueOf(inst.value, ctx)?.let { aliasSetFromInfo(it.aliasInfo()) }
            ?: unknown(inst.location.index, ctx)
        return state.removeOldAndMergeWith(global.aliasInfo().index(), valueSet)
    }

    private fun evalContainerStore(container: GoIRValue, value: GoIRValue, state: State, ctx: ContextInfo): State {
        val instance = refValueOf(container, ctx) ?: return state
        val valueRv = refValueOf(value, ctx) ?: return state
        val heapAlias = HeapAlias(state.heapObj(instance.aliasInfo()), GoArrayAlias).index()
        return state.mergeWith(heapAlias, valueRv.aliasInfo().index())
    }

    private fun evalPhi(inst: GoIRPhi, state: State, ctx: ContextInfo): State {
        val lhs = registerLocal(inst.register, ctx).aliasInfo().index()
        var result = state.remove(lhs)
        for (value in inst.edges.values) {
            val rv = refValueOf(value, ctx) ?: continue
            result = result.mergeWith(lhs, rv.aliasInfo().index())
        }
        return result
    }

    private fun evalMakeClosure(inst: GoIRAssignInst, expr: GoIRMakeClosureExpr, state: State, gas: GraphAnalysisState): State {
        val ctx = gas.ctx
        val instIdx = inst.location.index
        val alloc = GoLocalAlias.Alloc(instIdx, ctx)
        closureAllocFns[alloc] = expr.fn
        val closure = registerLocal(inst.register, ctx)
        var result = state.removeOldAndMergeWith(closure.aliasInfo().index(), aliasSetFromInfo(alloc))
        for ((i, binding) in expr.bindings.withIndex()) {
            val b = refValueOf(binding, ctx) ?: continue
            val heapAlias = HeapAlias(result.heapObj(closure.aliasInfo()), GoFieldAlias(freeVarField(expr.fn, i))).index()
            result = result.mergeWith(heapAlias, b.aliasInfo().index())
        }
        return result
    }

    private fun evalCall(inst: GoIRCall, state: State, gas: GraphAnalysisState): State {
        val callerCtx = gas.ctx
        val candidates = resolveCallTargets(inst.call, state, callerCtx)
        if (candidates != null) {
            val resolved = resolveCall(inst.location.index, candidates, callerCtx)
            if (resolved != null) {
                val r = evalResolvedCall(inst, state, resolved, callerCtx)
                if (r != null) return r
            }
        }
        return unresolvedCall(inst, state, callerCtx)
    }

    private fun unresolvedCall(inst: GoIRCall, state: State, callerCtx: ContextInfo): State {
        val lhs = registerLocal(inst.register, callerCtx).aliasInfo().index()
        return state.removeOldAndMergeWith(lhs, aliasSetFromInfo(GoReturnValue(inst.location.index, callerCtx)))
    }

    private fun resolveCallTargets(
        call: GoIRCallInfo,
        state: State,
        ctx: ContextInfo,
    ): List<Pair<GoIRFunction, GoRefValue?>>? = when (call.mode) {
        GoIRCallMode.DIRECT -> {
            val fn = (call.target as? GoIRCallTarget.Function)?.function ?: return null
            listOf(fn to null)
        }

        GoIRCallMode.DYNAMIC -> {
            val value = (call.target as? GoIRCallTarget.Dynamic)?.value ?: return null
            val rv = refValueOf(value, ctx) ?: return null
            val fns = mutableListOf<Pair<GoIRFunction, GoRefValue?>>()
            state.forEachAliasInSet(rv.aliasInfo().index()) { id ->
                val info = aliasManager.getElementUncheck(id)
                if (info is GoLocalAlias.Alloc) {
                    val fn = closureAllocFns[info]
                    if (fn != null) fns.add(fn to rv)
                }
            }
            fns.ifEmpty { null }
        }

        GoIRCallMode.INVOKE -> null
    }

    private fun resolveCall(
        callInstIdx: Int,
        candidates: List<Pair<GoIRFunction, GoRefValue?>>,
        callerCtx: ContextInfo,
    ): List<GoResolvedCallMethod>? {
        if (callerCtx.level >= interProcCallDepth) return null
        if (candidates.isEmpty()) return null
        val resolved = candidates.mapIndexed { idx, (fn, closure) ->
            if (!fn.hasBody) return null
            val graph = graphOf(fn) ?: return null
            val nestedCtx = ContextInfo(callerCtx.context + (callInstIdx * 1000 + idx))
            GoResolvedCallMethod(fn, graph, nestedCtx, closure)
        }
        return resolved
    }

    private fun evalResolvedCall(
        inst: GoIRCall,
        state: State,
        methods: List<GoResolvedCallMethod>,
        callerCtx: ContextInfo,
    ): State? {
        val before = state.asImmutable()
        val after = mutableListOf<ImmutableState>()
        for (m in methods) {
            bindCall(inst.call, m, callerCtx)
            val gas = GraphAnalysisState(m.graph.statements.size, m.ctx, m.function)
            analyze(m.graph, before, gas)
            after += mapCallFinalStates(gas, m.graph, inst, callerCtx)
        }
        if (after.isEmpty()) return null
        if (after.size == 1) return after.first().mutableCopy()
        return State.merge(aliasManager, dsuMergeStrategy, after)
    }

    private fun bindCall(call: GoIRCallInfo, m: GoResolvedCallMethod, callerCtx: ContextInfo) {
        val args = buildList {
            call.receiver?.let { add(it) }
            addAll(call.args)
        }
        calleeArgMap[m.ctx] = args.map { refValueOf(it, callerCtx) }
        calleeClosure[m.ctx] = m.closureValue
    }

    private fun mapCallFinalStates(
        gas: GraphAnalysisState,
        graph: GoInstGraph,
        callInst: GoIRCall,
        callerCtx: ContextInfo,
    ): List<ImmutableState> =
        graph.statements.filterIsInstance<GoIRReturn>().mapNotNull { ret ->
            val finalState = gas.stateAfterStmt[ret.location.index] ?: return@mapNotNull null
            val retVal = ret.results.firstOrNull()?.let { refValueOf(it, gas.ctx) }
            createStateAfterCall(finalState, callInst, retVal, callerCtx)
        }

    private fun createStateAfterCall(
        finalState: ImmutableState,
        callInst: GoIRCall,
        retVal: GoRefValue?,
        callerCtx: ContextInfo,
    ): ImmutableState {
        var state = finalState.mutableCopy()
        if (retVal != null) {
            val outer = registerLocal(callInst.register, callerCtx).aliasInfo().index()
            state = state.removeOldAndMergeWith(outer, aliasSetFromInfo(retVal.aliasInfo()))
        }
        return removeCallLocals(state, callerCtx.level).asImmutable()
    }

    private fun removeCallLocals(state: State, level: Int): State {
        val toRemove = IntOpenHashSet()
        state.allElements().forEachInt { idx ->
            if (isCallLocal(aliasManager.getElementUncheck(idx), level)) toRemove.add(idx)
        }
        return state.removeUnsafe(toRemove)
    }

    private fun isCallLocal(info: AAInfo, level: Int): Boolean = when (info) {
        is GoLocalAlias.Alloc -> false
        is GoUnknown -> info.ctx.level > level
        is GoReturnValue -> info.ctx.level > level
        is GoLocalAlias.SimpleLoc -> {
            val loc = info.loc
            loc is GoRefValue.Local && loc.ctx.level > level
        }
        is HeapAlias -> false
        else -> false
    }

    private fun graphOf(fn: GoIRFunction): GoInstGraph? = graphCache.getOrPut(fn) { GoCompactGraphBuilder.build(fn) }

    private fun refValueOf(value: GoIRValue, ctx: ContextInfo): GoRefValue? = when (value) {
        is GoIRRegister -> GoRefValue.Local(value.index, ctx)
        is GoIRParameterValue ->
            if (ctx == ContextInfo.rootContext) GoRefValue.Arg(value.paramIndex)
            else calleeArgMap[ctx]?.getOrNull(value.paramIndex)
        else -> null
    }

    private fun freeVarValue(ctx: ContextInfo): GoRefValue {
        calleeClosure[ctx]?.let { return it }
        if (ctx == ContextInfo.rootContext) return GoRefValue.FreeVarBase

        error("Unbound free var in non-root context")
    }

    private fun registerLocal(register: GoIRRegister, ctx: ContextInfo): GoRefValue.Local =
        GoRefValue.Local(register.index, ctx)

    private fun GoRefValue.aliasInfo(): AAInfo = GoLocalAlias.SimpleLoc(this)

    private fun AAInfo.index(): Int = aliasManager.getOrAdd(this)

    private fun aliasSetFromInfo(info: AAInfo): AliasSet = AliasSet(info.index())

    private fun unknown(instIdx: Int, ctx: ContextInfo): AliasSet = aliasSetFromInfo(GoUnknown(instIdx, ctx))

    private fun structFieldAccessor(structVal: GoIRValue, fieldName: String): GoAliasAccessor.Field =
        GoAliasAccessor.Field(structVal.type.typeName.removePrefix("*"), fieldName)

    private fun freeVarField(fn: GoIRFunction, slot: Int): GoAliasAccessor.Field {
        val accessor = GoFlowFunctionUtils.freeVarAccessor(fn, slot)
        return GoAliasAccessor.Field(accessor.className, accessor.fieldName)
    }

    private fun State.heapObj(instance: AAInfo): Int = aliasGroupId(instance.index())

    private fun State.remove(element: Int): State {
        val info = aliasManager.getElementUncheck(element)
        if (info is GoUnknown) return this
        return removeUnsafe(IntOpenHashSet.of(element))
    }

    private fun State.removeOldAndMergeWith(info: Int, alias: AliasSet): State =
        remove(info).mergeAliasSets(IntOpenHashSet(intArrayOf(info, alias.repr)))

    private fun State.mergeWith(info: Int, other: Int): State =
        mergeAliasSets(IntOpenHashSet(intArrayOf(info, other)))

    private fun State.containsMultipleConcreteOrOuterLocations(infoIdx: Int, visited: IntOpenHashSet): Boolean {
        val instances = IntArrayList()
        forEachAliasInSet(infoIdx) { instances.add(it) }
        var concrete = 0
        val it = instances.iterator()
        while (it.hasNext()) {
            val idx = it.nextInt()
            if (visited.contains(idx)) return true
            when (val info = aliasManager.getElementUncheck(idx)) {
                is GoReturnValue -> return true
                is GoUnknown -> return true
                is HeapAlias -> {
                    visited.add(idx)
                    if (containsMultipleConcreteOrOuterLocations(aliasGroupRepr(info.instance), visited)) return true
                    concrete++
                }
                is GoLocalAlias.Alloc -> concrete++
                is GoLocalAlias.SimpleLoc -> {
                    val loc = info.loc
                    if (loc is GoRefValue.Arg || loc is GoRefValue.Global) return true
                }
            }
        }
        return concrete > 1
    }
}
