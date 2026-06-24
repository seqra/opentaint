package org.opentaint.dataflow.jvm.ap.ifds.alias

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import mu.KLogging
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.graph.CompactGraph
import org.opentaint.dataflow.graph.MethodInstGraph
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAllocInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.alias.RefValue.Local
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRStringConstant
import org.opentaint.jvm.graph.JApplicationGraph
import org.opentaint.util.analysis.ApplicationGraph

class JIRIntraProcAliasAnalysis(
    private val entryPoint: JIRInst,
    private val graph: JApplicationGraph,
    private val callResolver: JIRCallResolver,
    private val languageManager: JIRLanguageManager,
    private val rootCancellation: Cancellation,
    private val params: JIRLocalAliasAnalysis.Params,
) {
    companion object {
        private val logger = object : KLogging() {}.logger
        private const val HEAP_CHAIN_LIMIT = 5
    }

    data class JIRInstGraph(
        val statements: List<JIRInst>,
        val graph: CompactGraph,
        val initialIdx: Int,
    )

    private fun getJIG(entryPoint: JIRInst): JIRInstGraph {
        @Suppress("UNCHECKED_CAST")
        val instGraph = MethodInstGraph.build(
            languageManager,
            graph as ApplicationGraph<CommonMethod, CommonInst>,
            entryPoint.location.method
        )

        return JIRInstGraph(
            statements = instGraph.instructions.map { it as JIRInst },
            graph = instGraph.graph,
            initialIdx = languageManager.getInstIndex(entryPoint)
        )
    }

    private inner class CallResolver: JirCallResolver(callResolver, graph, params) {
        override fun buildMethodJig(entryPoint: JIRInst): JIRInstGraph = getJIG(entryPoint)
    }

    fun computeMay(
        localVariableReachability: JIRLocalVariableReachability
    ): JIRLocalAliasAnalysis.MethodAliasInfo =
        withAnalysisCancellation(
            timeLimit = params.aliasAnalysisTimeLimit,
            parentCancellation = rootCancellation,
            body = { computeMay(it, localVariableReachability) },
            onAnalysisCancelled = {
                logger.error {
                    "May alias analysis for ${entryPoint.location.method} exceed ${params.aliasAnalysisTimeLimit}"
                }

                JIRLocalAliasAnalysis.MethodAliasInfo(
                    aliasBeforeStatement = null,
                    aliasAfterStatement = null,
                    unboundBeforeStatement = null,
                )
            }
        )

    private fun computeMay(
        cancellation: AnalysisCancellation,
        localVariableReachability: JIRLocalVariableReachability
    ): JIRLocalAliasAnalysis.MethodAliasInfo {
        val jig = getJIG(entryPoint)
        val daa = DSUAliasAnalysis(CallResolver(), localVariableReachability, MergeType.May, cancellation).analyze(jig)

        val aliasBeforeStatement = Array(jig.statements.size) { Int2ObjectOpenHashMap<List<AliasInfo>>() }
        val aliasAfterStatement = Array(jig.statements.size) { Int2ObjectOpenHashMap<List<AliasInfo>>() }

        val unboundAliasBeforeStatement = Array(jig.statements.size) { mutableListOf<List<AliasInfo>>() }
        val unboundAliasAfterStatement = Array(jig.statements.size) { mutableListOf<List<AliasInfo>>() }

        val manager = daa.manager

        for (i in jig.statements.indices) {
            resolveLocalVar(
                daa.statesBeforeStmt[i] as State, manager, localVariableReachability,
                aliasBeforeStatement[i], unboundAliasBeforeStatement[i],
                i, cancellation
            )

            resolveLocalVar(
                daa.statesAfterStmt[i] as State, manager, localVariableReachability,
                aliasAfterStatement[i], unboundAliasAfterStatement[i],
                i, cancellation
            )
        }

        return compressAliasInfo(aliasBeforeStatement, aliasAfterStatement, unboundAliasBeforeStatement)
    }

    fun computeMust(
        localVariableReachability: JIRLocalVariableReachability
    ): JIRLocalAliasAnalysis.MethodMustAliasInfo =
        withAnalysisCancellation(
            timeLimit = params.aliasAnalysisTimeLimit,
            parentCancellation = rootCancellation,
            body = { computeMust(it, localVariableReachability) },
            onAnalysisCancelled = {
                logger.error {
                    "Must alias analysis for ${entryPoint.location.method} exceed ${params.aliasAnalysisTimeLimit}"
                }

                JIRLocalAliasAnalysis.MethodMustAliasInfo(
                    aliasBeforeStatement = null,
                    aliasAfterStatement = null,
                    unboundBeforeStatement = null,
                )
            }
        )

    private fun computeMust(
        cancellation: AnalysisCancellation,
        localVariableReachability: JIRLocalVariableReachability
    ): JIRLocalAliasAnalysis.MethodMustAliasInfo {
        val jig = getJIG(entryPoint)
        val daa = DSUAliasAnalysis(CallResolver(), localVariableReachability, MergeType.Must, cancellation).analyze(jig)

        val aliasBeforeStatement = Array(jig.statements.size) { Object2ObjectOpenHashMap<AccessPathBase, List<AliasInfo>>() }
        val aliasAfterStatement = Array(jig.statements.size) { Object2ObjectOpenHashMap<AccessPathBase, List<AliasInfo>>() }

        val unboundAliasBeforeStatement = Array(jig.statements.size) { mutableListOf<List<AliasInfo>>() }
        val unboundAliasAfterStatement = Array(jig.statements.size) { mutableListOf<List<AliasInfo>>() }

        val manager = daa.manager

        for (i in jig.statements.indices) {
            resolveAccessPathBase(
                daa.statesBeforeStmt[i] as State, manager, localVariableReachability,
                aliasBeforeStatement[i], unboundAliasBeforeStatement[i],
                i, cancellation
            )

            resolveAccessPathBase(
                daa.statesAfterStmt[i] as State, manager, localVariableReachability,
                aliasAfterStatement[i], unboundAliasAfterStatement[i],
                i, cancellation
            )
        }

        return compressMustAliasInfo(aliasBeforeStatement, aliasAfterStatement, unboundAliasBeforeStatement)
    }

    private fun compressAliasInfo(
        aliasBeforeStatement: Array<Int2ObjectOpenHashMap<List<AliasInfo>>>,
        aliasAfterStatement: Array<Int2ObjectOpenHashMap<List<AliasInfo>>>,
        unboundBeforeStatement: Array<MutableList<List<AliasInfo>>>,
    ): JIRLocalAliasAnalysis.MethodAliasInfo {
        val compressedBefore = arrayOfNulls<Int2ObjectOpenHashMap<Array<Any>>>(aliasBeforeStatement.size)
        val compressedAfter = arrayOfNulls<Int2ObjectOpenHashMap<Array<Any>>>(aliasAfterStatement.size)

        compress(aliasBeforeStatement, compressedBefore, reference = null, referenceCompressed = null)
        compress(aliasAfterStatement, compressedAfter, aliasBeforeStatement, compressedBefore)

        val compressedUnbound = compressUnboundAliases(unboundBeforeStatement)
        return JIRLocalAliasAnalysis.MethodAliasInfo(compressedBefore, compressedAfter, compressedUnbound)
    }

    private fun compressUnboundAliases(
        statementInfo: Array<MutableList<List<AliasInfo>>>
    ): Array<Array<Array<Any>>?>? {
        if (statementInfo.all { it.isEmpty() }) return null

        val compressed = arrayOfNulls<Array<Array<Any>>>(statementInfo.size)
        for (i in statementInfo.indices) {
            val current = statementInfo[i]
            if (current.isEmpty()) continue

            if (i > 0 && statementInfo[i - 1] == current) {
                compressed[i] = compressed[i - 1]
                continue
            }

            val unwrapped = Array(current.size) { i ->
                JIRLocalAliasAnalysis.unwrapAliasSet(current[i])
            }
            compressed[i] = unwrapped
        }
        return compressed
    }

    private fun compressMustAliasInfo(
        aliasBeforeStatement: Array<Object2ObjectOpenHashMap<AccessPathBase, List<AliasInfo>>>,
        aliasAfterStatement: Array<Object2ObjectOpenHashMap<AccessPathBase, List<AliasInfo>>>,
        unboundBeforeStatement: Array<MutableList<List<AliasInfo>>>,
    ): JIRLocalAliasAnalysis.MethodMustAliasInfo {
        val compressedBefore = arrayOfNulls<Object2ObjectOpenHashMap<AccessPathBase, Array<Any>>>(aliasBeforeStatement.size)
        val compressedAfter = arrayOfNulls<Object2ObjectOpenHashMap<AccessPathBase, Array<Any>>>(aliasAfterStatement.size)

        compress(aliasBeforeStatement, compressedBefore, reference = null, referenceCompressed = null)
        compress(aliasAfterStatement, compressedAfter, aliasBeforeStatement, compressedBefore)

        val compressedUnbound = compressUnboundAliases(unboundBeforeStatement)
        return JIRLocalAliasAnalysis.MethodMustAliasInfo(compressedBefore, compressedAfter, compressedUnbound)
    }

    private fun compress(
        statementInfo: Array<Int2ObjectOpenHashMap<List<AliasInfo>>>,
        compressed: Array<Int2ObjectOpenHashMap<Array<Any>>?>,
        reference: Array<Int2ObjectOpenHashMap<List<AliasInfo>>>?,
        referenceCompressed: Array<Int2ObjectOpenHashMap<Array<Any>>?>?
    ) {
        for (i in statementInfo.indices) {
            val current = statementInfo[i]
            if (current.isEmpty()) continue

            if (i > 0 && statementInfo[i - 1] == current) {
                compressed[i] = compressed[i - 1]
                continue
            }

            if (reference != null) {
                if (reference[i] == current) {
                    compressed[i] = referenceCompressed!![i]
                }

                if (i > 0 && reference[i - 1] == current) {
                    compressed[i] = referenceCompressed!![i - 1]
                    continue
                }
            }

            val unwrapped = JIRLocalAliasAnalysis.unwrapAllInfo(current)
            compressed[i] = unwrapped
        }
    }

    private fun compress(
        statementInfo: Array<Object2ObjectOpenHashMap<AccessPathBase, List<AliasInfo>>>,
        compressed: Array<Object2ObjectOpenHashMap<AccessPathBase, Array<Any>>?>,
        reference: Array<Object2ObjectOpenHashMap<AccessPathBase, List<AliasInfo>>>?,
        referenceCompressed: Array<Object2ObjectOpenHashMap<AccessPathBase, Array<Any>>?>?
    ) {
        for (i in statementInfo.indices) {
            val current = statementInfo[i]
            if (current.isEmpty()) continue

            if (i > 0 && statementInfo[i - 1] == current) {
                compressed[i] = compressed[i - 1]
                continue
            }

            if (reference != null) {
                if (reference[i] == current) {
                    compressed[i] = referenceCompressed!![i]
                }

                if (i > 0 && reference[i - 1] == current) {
                    compressed[i] = referenceCompressed!![i - 1]
                    continue
                }
            }

            val unwrapped = JIRLocalAliasAnalysis.unwrapAllInfo(current)
            compressed[i] = unwrapped
        }
    }

    private fun State.getAliasIndexesFor(root: Int, storage: IntOpenHashSet) {
        forEachAliasInSet(root) { storage.add(it.ensureNonLValue()) }
    }

    private fun State.getAliasIndexesFor(root: Int): IntOpenHashSet {
        val aliases = IntOpenHashSet()
        getAliasIndexesFor(root, aliases)
        return aliases
    }

    private fun State.getAliasesFor(root: Int, manager: AAInfoManager): List<AAInfo> {
        return getAliasIndexesFor(root).map { manager.getElementUncheck(it) }
    }

    private inline fun saveConvertedAliases(
        root: Int,
        state: State,
        manager: AAInfoManager,
        reachableLocals: JIRLocalVariableReachability,
        instIdx: Int,
        cancellation: AnalysisCancellation,
        bound: HashSet<Int>,
        save: (List<AliasInfo>) -> Unit
    ) {
        val aliases = state.getAliasIndexesFor(root)
        val converted = aliases.map { manager.getElementUncheck(it) }
            .flatMap { it.convertToAliasInfo(state, manager, depth = 0, cancellation) }
            .filter { it !is AliasApInfo || reachableLocals.isReachable(it.base, instIdx) }
            .distinct()
        // size == 1 means only root was converted to AliasInfo; not really meaningful
        if (converted.size <= 1) return
        aliases.forEach { bound.add(it) }
        save(converted)
    }

    private fun resolveLocalVar(
        state: State,
        manager: AAInfoManager,
        reachableLocals: JIRLocalVariableReachability,
        result: Int2ObjectOpenHashMap<List<AliasInfo>>,
        unboundAliases: MutableList<List<AliasInfo>>,
        instIdx: Int,
        cancellation: AnalysisCancellation,
    ) {
        val bound = HashSet<Int>()

        val allElements = state.allNonLValueElements()

        allElements.forEachInt { infoIndex ->
            if (infoIndex.isLValue()) return@forEachInt

            val root = manager.getElementUncheck(infoIndex)
            if (root !is LocalAlias.SimpleLoc || root.loc !is Local || !reachableLocals.isReachable(root.loc.idx, instIdx))
                return@forEachInt

            saveConvertedAliases(infoIndex, state, manager, reachableLocals, instIdx, cancellation, bound) {
                result[root.loc.idx] = it
            }
        }

        allElements.forEachInt { infoIndex ->
            if (infoIndex.isLValue() || infoIndex in bound) return@forEachInt

            saveConvertedAliases(infoIndex, state, manager, reachableLocals, instIdx, cancellation, bound) {
                unboundAliases += it
            }
        }
    }

    private fun AAInfo.isMustRelevant() =
        this is LocalAlias.SimpleLoc && this.loc !is RefValue.Static

    private fun resolveAccessPathBase(
        state: State,
        manager: AAInfoManager,
        reachableLocals: JIRLocalVariableReachability,
        result: Object2ObjectOpenHashMap<AccessPathBase, List<AliasInfo>>,
        unboundAliases: MutableList<List<AliasInfo>>,
        instIdx: Int,
        cancellation: AnalysisCancellation,
    ) {
        val bound = HashSet<Int>()

        val allElements = state.allNonLValueElements()

        allElements.forEachInt { infoIndex ->
            if (infoIndex.isLValue()) return@forEachInt

            val root = manager.getElementUncheck(infoIndex)
            if (root.isMustRelevant())
                return@forEachInt

            val rootBase = (convertBaseAccessor(root)!! as AliasApInfo).base
            saveConvertedAliases(infoIndex, state, manager, reachableLocals, instIdx, cancellation, bound) {
                result[rootBase] = it
            }
        }

        allElements.forEachInt { infoIndex ->
            if (infoIndex.isLValue() || infoIndex in bound) return@forEachInt

            saveConvertedAliases(infoIndex, state, manager, reachableLocals, instIdx, cancellation, bound) {
                unboundAliases += it
            }
        }
    }

    private fun AAInfo.simpleConvertToAliasInfo(manager: AAInfoManager): AliasInfo? {
        if (this !is HeapAlias) {
            return convertBaseAccessor(this)
        }

        val accessors = mutableListOf<AliasAccessor>()
        var curInfo = this
        while (curInfo is HeapAlias) {
            val accessor = when (val a = curInfo.heapAccessor) {
                is ArrayAlias -> AliasAccessor.Array
                is FieldAlias -> a.field
            }
            accessors.add(accessor)
            curInfo = manager.getElementUncheck(curInfo.instance)
        }

        val instanceSimple = convertBaseAccessor(curInfo)
        if (instanceSimple !is AliasApInfo) return null

        return AliasApInfo(instanceSimple.base, accessors.reversed())
    }

    private fun AAInfo.collectAllAliases(
        state: State,
        manager: AAInfoManager,
        depth: Int,
        cancellation: AnalysisCancellation,
        visited: IntOpenHashSet = IntOpenHashSet(),
    ): List<AAInfo> {
        val index = manager.getOrAdd(this)
        if (!visited.add(index))
            return listOf(this)

        if (this !is HeapAlias) {
            return listOf(this)
        }

        if (depth > HEAP_CHAIN_LIMIT) {
            return emptyList()
        }

        cancellation.checkpoint()

        val instanceGroup = state.getAliasesFor(instance, manager)
        if (instanceGroup.isEmpty()) return emptyList()

        val instances = instanceGroup.flatMap { it.collectAllAliases(state, manager, depth + 1, cancellation, visited) }

        val bridgedAliases = instances.flatMap { instance ->
            val instanceIndex = manager.getOrAdd(instance)
            val heapInstance = HeapAlias(instanceIndex, this.heapAccessor)
            val heapIndex = manager.getOrAdd(heapInstance)
            val heapAliases = state.getAliasesFor(heapIndex, manager)
            heapAliases.flatMap { it.collectAllAliases(state, manager, depth, cancellation, visited) }
        }

        return bridgedAliases
    }

    private fun AAInfo.convertToAliasInfo(
        state: State,
        manager: AAInfoManager,
        depth: Int,
        cancellation: AnalysisCancellation,
    ): List<AliasInfo> =
        collectAllAliases(state, manager, depth, cancellation).mapNotNull { it.simpleConvertToAliasInfo(manager) }

    private fun convertBaseAccessor(cur: AAInfo): AliasInfo? {
        if (cur.ctx != ContextInfo.rootContext) return null

        val base = when (cur) {
            is LocalAlias.SimpleLoc -> when (val loc = cur.loc) {
                is Local -> AccessPathBase.LocalVar(loc.idx)
                is RefValue.Arg -> AccessPathBase.Argument(loc.idx)
                is RefValue.This -> AccessPathBase.This
                is RefValue.Static -> {
                    val staticAccessors = listOf(AliasAccessor.Static(loc.type))
                    return AliasApInfo(AccessPathBase.ClassStatic, staticAccessors)
                }
            }

            is LocalAlias.Alloc -> {
                val assignedExpr = cur.stmt.assignedExpr()
                    ?: return null

                val const = assignedExpr as? SimpleValue.RefConst

                val stringConst = const?.expr as? JIRStringConstant
                    ?: return AliasAllocInfo(cur.stmt.originalIdx)

                AccessPathBase.Constant("java.lang.String", stringConst.value)
            }

            is CallReturn,
            is Unknown -> return null

            is LValue,
            is HeapAlias -> error("unreachable")
        }

        return AliasApInfo(base, emptyList())
    }

    private fun Stmt.assignedExpr(): Expr? = when (this) {
        is Stmt.Assign -> expr
        is Stmt.FieldStore -> value as? Expr
        is Stmt.ArrayStore -> value as? Expr
        is Stmt.WriteStatic -> value as? Expr
        else -> null
    }
}
