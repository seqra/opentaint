package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfoManager
import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisResult
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.HeapAlias
import org.opentaint.dataflow.ap.ifds.analysis.alias.ImmutableState
import org.opentaint.dataflow.ap.ifds.analysis.alias.State
import org.opentaint.dataflow.jvm.ap.ifds.alias.ArrayAlias
import org.opentaint.dataflow.jvm.ap.ifds.alias.FieldAlias
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRIntraProcAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRIntraProcAliasAnalysis.Convert.convertToAliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.alias.LocalAlias
import org.opentaint.dataflow.jvm.ap.ifds.alias.RefValue
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JApplicationGraph
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

class JIRLocalAliasAnalysis(
    private val entryPoint: JIRInst,
    private val graph: JApplicationGraph,
    private val callResolver: JIRCallResolver,
    private val localVariableReachability: JIRLocalVariableReachability,
    private val cancellation: Cancellation,
    private val languageManager: JIRLanguageManager,
    private val params: Params,
) {
    data class Params(
        val useAliasAnalysis: Boolean = true,
        val aliasAnalysisInterProcCallDepth: Int = 0,
        val aliasAnalysisTimeLimit: Duration = 10.seconds,
    )

    private val aliasInfo: AnalysisResult? by lazy { compute() }

    fun findAlias(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? =
        stateBeforeStatement(statement)?.run { findLocalAlias(manager, base.idx) }

    fun findAliasAfterStatement(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? =
        stateAfterStatement(statement)?.run { findLocalAlias(manager, base.idx) }

    fun getAllAliasAtStatement(statement: CommonInst): List<List<AliasInfo>> =
        stateBeforeStatement(statement)?.run {
            convertAllAliasSets(manager)
        }.orEmpty()

    fun <F> forEachHeapAlias(
        base: AccessPathBase.LocalVar,
        statement: CommonInst,
        fact: F,
        next: (F) -> List<Pair<AliasAccessor, F>>,
        handle: (AliasInfo, F) -> Unit,
    ) {
        stateBeforeStatement(statement)?.apply {
            findHeapAlias(manager, base.idx, fact, next, handle)
        }
    }

    private fun stateBeforeStatement(statement: CommonInst): State? =
        getStatementState(statement) { statesBeforeStmt }

    private fun stateAfterStatement(statement: CommonInst): State? =
        getStatementState(statement) { statesAfterStmt }

    private inline fun getStatementState(
        statement: CommonInst,
        states: AnalysisResult.() -> Array<ImmutableState?>
    ): State? {
        val res = aliasInfo ?: return null

        val idx = languageManager.getInstIndex(statement)
        val state = res.states().getOrNull(idx)
            ?: return null

        return state.unsafeState()
    }

    private fun <F> State.findHeapAlias(
        manager: AAInfoManager,
        localIdx: Int,
        fact: F,
        next: (F) -> List<Pair<AliasAccessor, F>>,
        handle: (AliasInfo, F) -> Unit,
    ) {
        val localInfo = LocalAlias.SimpleLoc(RefValue.Local(localIdx, ContextInfo.rootContext))
        val localInfoIdx = manager.find(localInfo) ?: return

        findHeapAlias(manager, hashSetOf(), localInfoIdx, fact, next, handle)
    }

    private fun <F> State.findHeapAlias(
        manager: AAInfoManager,
        visited: MutableSet<F>,
        factInfo: Int,
        fact: F,
        next: (F) -> List<Pair<AliasAccessor, F>>,
        handle: (AliasInfo, F) -> Unit,
    ) {
        if (!visited.add(fact)) return

        convertAllAliases(factInfo, manager).forEach { handle(it, fact) }

        val instance = aliasGroupId(factInfo)
        for ((accessor, nextFact) in next(fact)) {
            val heapAccessors = when (accessor) {
                is AliasAccessor.Array -> listOf(ArrayAlias)
                is AliasAccessor.Field -> listOf(FieldAlias(accessor, false), FieldAlias(accessor, true))
                is AliasAccessor.Static -> continue
            }

            for (ha in heapAccessors) {
                val info = HeapAlias(instance, ha)
                val heapIdx = manager.find(info) ?: continue
                findHeapAlias(manager, visited, heapIdx, nextFact, next, handle)
            }
        }
    }

    private fun State.findLocalAlias(manager: AAInfoManager, localIdx: Int): List<AliasInfo>? {
        val localInfo = LocalAlias.SimpleLoc(RefValue.Local(localIdx, ContextInfo.rootContext))
        val localInfoIdx = manager.find(localInfo) ?: return null
        return convertAllAliases(localInfoIdx, manager)
    }

    private fun State.convertAllAliases(
        infoIdx: Int,
        manager: AAInfoManager
    ): List<AliasInfo> {
        val result = mutableListOf<AliasInfo>()
        forEachAliasInSet(infoIdx) { aliasIdx ->
            if (aliasIdx != infoIdx) {
                result += convert(aliasIdx, manager, depth = 0)
            }
        }
        return result
    }

    private fun State.convertAllAliasSets(
        manager: AAInfoManager
    ): List<List<AliasInfo>> = allAliasSets().map { aliasSet ->
        val result = mutableListOf<AliasInfo>()
        aliasSet.forEach {
            result += convert(it, manager, depth = 0)
        }
        result
    }

    private fun State.convert(infoIdx: Int, manager: AAInfoManager, depth: Int): List<AliasInfo> =
        convert(manager.getElementUncheck(infoIdx), manager, depth)

    private fun State.convert(info: AAInfo, manager: AAInfoManager, depth: Int): List<AliasInfo> =
        info.convertToAliasInfo(depth, null) { instance ->
            val instances = mutableListOf<AliasInfo>()
            forEachAliasInSet(instance) {
                instances += convert(it, manager, depth + 1)
            }
            instances
        }

    private fun compute(): AnalysisResult? {
        val analysis = JIRIntraProcAliasAnalysis(entryPoint, graph, callResolver, languageManager, cancellation, params)
        return analysis.compute(localVariableReachability)
    }

    sealed interface AliasAccessor {
        data class Field(val className: String, val fieldName: String, val fieldType: String) : AliasAccessor
        data object Array : AliasAccessor
        data class Static(val typeName: String) : AliasAccessor
    }

    sealed interface AliasInfo
    data class AliasApInfo(val base: AccessPathBase, val accessors: List<AliasAccessor>): AliasInfo
    data class AliasAllocInfo(val allocInst: Int): AliasInfo
}
