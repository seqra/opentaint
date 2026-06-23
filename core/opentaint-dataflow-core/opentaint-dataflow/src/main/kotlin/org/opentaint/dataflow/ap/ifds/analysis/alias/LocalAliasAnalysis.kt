package org.opentaint.dataflow.ap.ifds.analysis.alias

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.util.getOrCreate
import org.opentaint.dataflow.util.int2ObjectMap
import org.opentaint.ir.api.common.cfg.CommonInst

abstract class LocalAliasAnalysis<AliasInfo, AliasAccessor> {
    interface CommonAliasApInfo<AliasAccessor> {
        val base: AccessPathBase
        val accessors: List<AliasAccessor>
    }

    abstract fun compute(): AnalysisResult?

    val aliasInfo: AnalysisResult? by lazy { compute() }

    val convertedAliases = int2ObjectMap<List<AliasInfo>>()

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

    abstract fun getInstIndex(statement: CommonInst): Int

    private inline fun getStatementState(
        statement: CommonInst,
        states: AnalysisResult.() -> Array<ImmutableState?>
    ): State? {
        val res = aliasInfo ?: return null

        val idx = getInstIndex(statement)
        val state = res.states().getOrNull(idx)
            ?: return null

        return state.unsafeState()
    }

    abstract fun localInfo(localIdx: Int): AAInfo

    private fun <F> State.findHeapAlias(
        manager: AAInfoManager,
        localIdx: Int,
        fact: F,
        next: (F) -> List<Pair<AliasAccessor, F>>,
        handle: (AliasInfo, F) -> Unit,
    ) {
        val localInfo = localInfo(localIdx)
        val localInfoIdx = manager.find(localInfo) ?: return

        findHeapAlias(manager, hashSetOf(), localInfoIdx, fact, next, handle)
    }

    abstract fun convertAliasAccessor(aa: AliasAccessor): List<AAHeapAccessor>

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
            val heapAccessors = convertAliasAccessor(accessor)

            for (ha in heapAccessors) {
                val info = HeapAlias(instance, ha)
                val heapIdx = manager.find(info) ?: continue
                findHeapAlias(manager, visited, heapIdx, nextFact, next, handle)
            }
        }

        visited.remove(fact)
    }

    private fun State.findLocalAlias(manager: AAInfoManager, localIdx: Int): List<AliasInfo>? {
        val localInfo = localInfo(localIdx)
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

    abstract fun convert(info: AAInfo, depth: Int, convertInstance: (Int) -> List<AliasInfo>): List<AliasInfo>

    private fun State.convert(infoIdx: Int, manager: AAInfoManager, depth: Int): List<AliasInfo> =
        synchronized(this@LocalAliasAnalysis) {
            convertedAliases.getOrCreate(infoIdx) {
                convert(manager.getElementUncheck(infoIdx), manager, depth)
            }
        }

    private fun State.convert(info: AAInfo, manager: AAInfoManager, depth: Int): List<AliasInfo> =
        convert(info, depth) { instance ->
            val instances = mutableListOf<AliasInfo>()
            forEachAliasInSet(instance) {
                instances += convert(it, manager, depth + 1)
            }
            instances
        }
}
