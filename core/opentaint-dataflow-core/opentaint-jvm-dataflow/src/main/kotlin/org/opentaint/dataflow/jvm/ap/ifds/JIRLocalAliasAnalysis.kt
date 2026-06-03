package org.opentaint.dataflow.jvm.ap.ifds

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRIntraProcAliasAnalysis
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
        val aliasAnalysisTimeLimit: Duration = Cancellation.getActiveDuration(10.seconds),
    )

    private val mayAliasInfo by lazy { computeMay() }
    private val mustAliasInfo by lazy { computeMust() }

    class MethodAliasInfo(
        val aliasBeforeStatement: Array<Int2ObjectOpenHashMap<Array<Any>>?>?,
        val aliasAfterStatement: Array<Int2ObjectOpenHashMap<Array<Any>>?>?,
        val unboundBeforeStatement: Array<Array<Array<Any>>?>?,
    )

    class MethodMustAliasInfo(
        val aliasBeforeStatement: Array<Object2ObjectOpenHashMap<AccessPathBase, Array<Any>>?>?,
        val aliasAfterStatement: Array<Object2ObjectOpenHashMap<AccessPathBase, Array<Any>>?>?,
        val unboundBeforeStatement: Array<Array<Array<Any>>?>?,
    )

    private fun getLocalVarAliases(
        alias: Array<Int2ObjectOpenHashMap<Array<Any>>?>,
        instIdx: Int, base: AccessPathBase.LocalVar
    ): List<AliasInfo>? =
        alias[instIdx]?.getOrDefault(base.idx, null)?.filter {
            it !is AccessPathBase || it != base
        }?.map { it.wrapAliasInfo() }

    private fun getAccessPathBaseAliases(
        alias: Array<Object2ObjectOpenHashMap<AccessPathBase, Array<Any>>?>,
        instIdx: Int, base: AccessPathBase
    ): List<AliasInfo>? =
        alias[instIdx]?.getOrDefault(base, null)?.filter {
            it !is AccessPathBase || it != base
        }?.map { it.wrapAliasInfo() }

    fun findMustAlias(base: AccessPathBase, statement: CommonInst): List<AliasInfo>? {
        val aliasBefore = mustAliasInfo.aliasBeforeStatement ?: return null
        val idx = languageManager.getInstIndex(statement)
        return getAccessPathBaseAliases(aliasBefore, idx, base)
    }

    fun findMustAliasAfterStatement(base: AccessPathBase, statement: CommonInst): List<AliasInfo>? {
        val aliasBefore = mustAliasInfo.aliasAfterStatement ?: return null
        val idx = languageManager.getInstIndex(statement)
        return getAccessPathBaseAliases(aliasBefore, idx, base)
    }

    fun findAlias(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? {
        val aliasBefore = mayAliasInfo.aliasBeforeStatement ?: return null
        val idx = languageManager.getInstIndex(statement)
        return getLocalVarAliases(aliasBefore, idx, base)
    }

    fun getAllAliasAtStatement(statement: CommonInst): List<List<AliasInfo>> {
        val result = mutableListOf<List<AliasInfo>>()
        val idx = languageManager.getInstIndex(statement)

        mayAliasInfo.aliasBeforeStatement?.let { aliasBefore ->
            aliasBefore[idx]?.let { wrapAllInfo(it) }?.let { result.addAll(it.values) }
        }

        mayAliasInfo.unboundBeforeStatement?.let { unboundBefore ->
            unboundBefore[idx]?.let { aliases -> aliases.map { wrapAliasSet(it) } }?.let { result.addAll(it) }
        }

        return result
    }

    fun findAliasAfterStatement(base: AccessPathBase.LocalVar, statement: CommonInst): List<AliasInfo>? {
        val aliasAfter = mayAliasInfo.aliasAfterStatement ?: return null
        val idx = languageManager.getInstIndex(statement)
        return getLocalVarAliases(aliasAfter, idx, base)
    }

    private fun computeMay(): MethodAliasInfo {
        val analysis = JIRIntraProcAliasAnalysis(entryPoint, graph, callResolver, languageManager, cancellation, params)
        return analysis.computeMay(localVariableReachability)
    }

    private fun computeMust(): MethodMustAliasInfo {
        val analysis = JIRIntraProcAliasAnalysis(entryPoint, graph, callResolver, languageManager, cancellation, params)
        return analysis.computeMust(localVariableReachability)
    }

    sealed interface AliasAccessor {
        data class Field(val className: String, val fieldName: String, val fieldType: String) : AliasAccessor
        data object Array : AliasAccessor
        data class Static(val typeName: String) : AliasAccessor
    }

    sealed interface AliasInfo
    data class AliasApInfo(val base: AccessPathBase, val accessors: List<AliasAccessor>): AliasInfo
    data class AliasAllocInfo(val allocInst: Int): AliasInfo

    companion object {
        fun AliasInfo.unwrap(): Any = when (this) {
            is AliasAllocInfo -> allocInst
            is AliasApInfo -> if (accessors.isEmpty()) base else this
        }

        fun Any.wrapAliasInfo(): AliasInfo = when (this) {
            is AccessPathBase -> AliasApInfo(this, emptyList())
            is AliasInfo -> this
            is Int -> AliasAllocInfo(this)
            else -> error("Impossible")
        }

        fun wrapAllInfo(info: Int2ObjectOpenHashMap<Array<Any>>): Int2ObjectOpenHashMap<List<AliasInfo>> {
            val result = Int2ObjectOpenHashMap<List<AliasInfo>>()
            for ((key, aliases) in info) {
                result.put(key, wrapAliasSet(aliases))
            }
            return result
        }

        fun wrapAliasSet(aliases: Array<Any>): List<AliasInfo> =
            List(aliases.size) { aliases[it].wrapAliasInfo() }

        fun wrapAllInfo(info: Object2ObjectOpenHashMap<AccessPathBase, Array<Any>>): Object2ObjectOpenHashMap<AccessPathBase, List<AliasInfo>> {
            val result = Object2ObjectOpenHashMap<AccessPathBase, List<AliasInfo>>()
            for ((key, aliases) in info) {
                result.put(key, wrapAliasSet(aliases))
            }
            return result
        }

        fun unwrapAllInfo(info: Int2ObjectOpenHashMap<List<AliasInfo>>): Int2ObjectOpenHashMap<Array<Any>> {
            val result = Int2ObjectOpenHashMap<Array<Any>>(info.size, 0.99f)
            val iter = info.int2ObjectEntrySet().fastIterator()
            while (iter.hasNext()) {
                val entry = iter.next()
                val unwrapped = unwrapAliasSet(entry.value)
                result.put(entry.intKey, unwrapped)
            }
            return result
        }

        fun unwrapAliasSet(aliases: List<AliasInfo>): Array<Any> =
            Array(aliases.size) { aliases[it].unwrap() }

        fun unwrapAllInfo(info: Object2ObjectOpenHashMap<AccessPathBase, List<AliasInfo>>): Object2ObjectOpenHashMap<AccessPathBase, Array<Any>> {
            val result = Object2ObjectOpenHashMap<AccessPathBase, Array<Any>>(info.size, 0.99f)
            val iter = info.object2ObjectEntrySet().fastIterator()
            while (iter.hasNext()) {
                val entry = iter.next()
                val unwrapped = unwrapAliasSet(entry.value)
                result.put(entry.key, unwrapped)
            }
            return result
        }
    }
}
