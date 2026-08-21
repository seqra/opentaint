package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAHeapAccessor
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisResult
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.HeapAlias
import org.opentaint.dataflow.ap.ifds.analysis.alias.LocalAliasAnalysis
import org.opentaint.dataflow.configuration.jvm.Argument
import org.opentaint.dataflow.configuration.jvm.ClassStatic
import org.opentaint.dataflow.configuration.jvm.CopyAllMarks
import org.opentaint.dataflow.configuration.jvm.Position
import org.opentaint.dataflow.configuration.jvm.PositionAccessor
import org.opentaint.dataflow.configuration.jvm.PositionWithAccess
import org.opentaint.dataflow.configuration.jvm.Result
import org.opentaint.dataflow.configuration.jvm.This
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.alias.ArrayAlias
import org.opentaint.dataflow.jvm.ap.ifds.alias.ExternalCallModelProvider
import org.opentaint.dataflow.jvm.ap.ifds.alias.ExternalCallModelProvider.ExternalAssign
import org.opentaint.dataflow.jvm.ap.ifds.alias.ExternalCallModelProvider.ExternalObject
import org.opentaint.dataflow.jvm.ap.ifds.alias.FieldAlias
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRIntraProcAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRIntraProcAliasAnalysis.Convert.convertToAliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRAliasPathCompressor
import org.opentaint.dataflow.jvm.ap.ifds.alias.LocalAlias
import org.opentaint.dataflow.jvm.ap.ifds.alias.RefValue
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRLocalVar
import org.opentaint.ir.api.jvm.ext.cfg.locals
import org.opentaint.jvm.graph.JApplicationGraph
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

class JIRLocalAliasAnalysis(
    private val entryPoint: JIRInst,
    private val graph: JApplicationGraph,
    private val callResolver: JIRCallResolver,
    private val modelProvider: TaintRulesProvider?,
    private val localVariableReachability: JIRLocalVariableReachability,
    private val cancellation: Cancellation,
    private val languageManager: JIRLanguageManager,
    private val factTypeChecker: JIRFactTypeChecker,
    private val params: Params,
) : LocalAliasAnalysis<AliasInfo, AliasAccessor>() {
    data class Params(
        val useAliasAnalysis: Boolean = true,
        val aliasAnalysisInterProcCallDepth: Int = 0,
        val aliasAnalysisTimeLimit: Duration = 10.seconds,
    )

    override fun getInstIndex(statement: CommonInst): Int =
        languageManager.getInstIndex(statement)

    override fun localInfo(localIdx: Int): AAInfo =
        LocalAlias.SimpleLoc(RefValue.Local(localIdx, ContextInfo.rootContext))

    override fun convertAliasAccessor(aa: AliasAccessor): List<AAHeapAccessor> = when (aa) {
        is AliasAccessor.Array -> listOf(ArrayAlias)
        is AliasAccessor.Field -> listOf(FieldAlias(aa, false), FieldAlias(aa, true))
        is AliasAccessor.Static -> emptyList()
    }

    override fun convert(
        info: AAInfo,
        depth: Int,
        convertInstance: (Int) -> List<AliasInfo>
    ): List<AliasInfo> = info
        .convertToAliasInfo(depth, null, ::isValidAccessorTransition, convertInstance)
        .filterNot { it is AliasApInfo && !isValidBaseAccessorTransition(it) }

    private fun isValidAccessorTransition(previous: AliasAccessor?, next: AliasAccessor): Boolean =
        isValidAliasAccessorTransition(previous, next, factTypeChecker::typeIsAssignableTo)

    private fun isValidBaseAccessorTransition(alias: AliasApInfo): Boolean {
        return isValidAliasBaseAccessorTransition(
            alias.base.typeName(),
            alias.accessors.firstOrNull(),
            factTypeChecker::typeIsAssignableTo,
        )
    }

    private val localTypes by lazy {
        entryPoint.location.method.instList.locals
            .filterIsInstance<JIRLocalVar>()
            .associate { it.index to it.type.typeName }
    }

    // Even small permutation sets multiply downstream IFDS facts, so compress every non-empty set.
    override val aliasCompressionThreshold: Int = 0

    override fun compressAliases(aliases: List<AliasInfo>): List<AliasInfo> =
        JIRAliasPathCompressor.compress(aliases, cancellation::checkpoint)

    override fun filterAliases(query: AAInfo, aliases: List<AliasInfo>): List<AliasInfo> {
        val queryType = query.typeName() ?: return aliases
        return aliases.filter { alias ->
            val aliasType = (alias as? AliasApInfo)?.typeName() ?: return@filter true
            isAliasResultTypeCompatible(queryType, aliasType, factTypeChecker::typeMayHaveSubtypeOf)
        }
    }

    private fun AAInfo.typeName(): String? = when (this) {
        is LocalAlias.SimpleLoc -> loc.typeName()
        is HeapAlias -> (heapAccessor as? FieldAlias)?.field?.fieldType
        else -> null
    }

    private fun AliasApInfo.typeName(): String? = when (val accessor = accessors.lastOrNull()) {
        is AliasAccessor.Field -> accessor.fieldType
        is AliasAccessor.Static -> accessor.typeName
        is AliasAccessor.Array -> null
        null -> base.typeName()
    }

    private fun RefValue.typeName(): String? = when (this) {
        is RefValue.Local -> if (ctx == ContextInfo.rootContext) localTypes[idx] else null
        is RefValue.Arg -> entryPoint.location.method.parameters.getOrNull(idx)?.type?.typeName
        is RefValue.This -> entryPoint.location.method.enclosingClass.name
        is RefValue.Static -> type
    }

    private fun AccessPathBase.typeName(): String? = when (this) {
        is AccessPathBase.Argument -> entryPoint.location.method.parameters.getOrNull(idx)?.type?.typeName
        is AccessPathBase.LocalVar -> localTypes[idx]
        is AccessPathBase.Constant -> typeName
        AccessPathBase.This -> entryPoint.location.method.enclosingClass.name
        else -> null
    }

    private inner class CallModelProvider : ExternalCallModelProvider {
        override fun provideModel(method: JIRMethod): List<ExternalAssign> {
            val rules = modelProvider?.passTroughRulesForMethod(method, null, null, false)?.toList().orEmpty()
            if (rules.isEmpty()) return emptyList()

            val actions = rules
                .flatMap { it.actionsAfter }
                .filterIsInstance<CopyAllMarks>()
                .distinct()

            val externalAssigns = actions.mapNotNull { action ->
                val from = action.from.toExternalObject() ?: return@mapNotNull null
                val to = action.to.toExternalObject() ?: return@mapNotNull null
                ExternalAssign(from, to)
            }

            return externalAssigns
        }

        private fun Position.toExternalObject(): ExternalObject? {
            val base = when (this) {
                is Argument -> ExternalCallModelProvider.Position.Arg(index)
                is Result -> ExternalCallModelProvider.Position.RetVal
                is This -> ExternalCallModelProvider.Position.This
                is PositionWithAccess -> {
                    val b = base.toExternalObject() ?: return null
                    val a = access.toAaAccessor() ?: return null
                    return ExternalObject(b.pos, b.accessors + a)
                }

                is ClassStatic -> return null
            }

            return ExternalObject(base, emptyList())
        }

        private fun PositionAccessor.toAaAccessor(): AAHeapAccessor? = when (this) {
            is PositionAccessor.AnyFieldAccessor -> null
            is PositionAccessor.ElementAccessor -> ArrayAlias
            is PositionAccessor.FieldAccessor -> {
                if (fieldName == "<rule-storage>") {
                    null
                } else {
                    FieldAlias(
                        AliasAccessor.Field(className, fieldName, fieldType),
                        isImmutable = false
                    )
                }
            }
        }
    }

    override fun compute(): AnalysisResult? {
        val analysis = JIRIntraProcAliasAnalysis(
            entryPoint, graph, callResolver,
            CallModelProvider(),
            languageManager, cancellation, params
        )
        return analysis.compute(localVariableReachability)
    }

    sealed interface AliasAccessor {
        data class Field(val className: String, val fieldName: String, val fieldType: String) : AliasAccessor
        data object Array : AliasAccessor
        data class Static(val typeName: String) : AliasAccessor
    }

    sealed interface AliasInfo

    data class AliasApInfo(
        override val base: AccessPathBase,
        override val accessors: List<AliasAccessor>
    ) : AliasInfo,
        CommonAliasApInfo<AliasAccessor>

    data class AliasAllocInfo(val allocInst: Int) : AliasInfo
}

internal fun isValidAliasAccessorTransition(
    previous: AliasAccessor?,
    next: AliasAccessor,
    typesMayOverlap: (String, String) -> Boolean,
): Boolean {
    if (previous is AliasAccessor.Array ||
        previous is AliasAccessor.Field && previous.fieldType == "java.lang.Object"
    ) {
        return false
    }

    if (next is AliasAccessor.Array) {
        return previous == null ||
            previous is AliasAccessor.Field && previous.fieldType.isArrayTypeName()
    }

    val field = next as? AliasAccessor.Field ?: return true
    if (previous != null && field.isErasedContainerAccessor()) return false

    val previousType = when (previous) {
        is AliasAccessor.Field -> previous.fieldType
        is AliasAccessor.Static -> previous.typeName
        is AliasAccessor.Array -> error("handled above")
        null -> return true
    }
    return typesMayOverlap(previousType, field.className)
}

private fun String.isArrayTypeName(): Boolean = endsWith("[]") || startsWith("[")

private fun AliasAccessor.Field.isErasedContainerAccessor(): Boolean =
    fieldType == "java.lang.Object" &&
        fieldName in ERASED_CONTAINER_ACCESSOR_NAMES

private val ERASED_CONTAINER_ACCESSOR_NAMES = setOf("Element", "MapKey", "MapValue")

internal fun isValidAliasBaseAccessorTransition(
    baseType: String?,
    first: AliasAccessor?,
    typesMayOverlap: (String, String) -> Boolean,
): Boolean {
    val field = first as? AliasAccessor.Field ?: return true
    return baseType == null || typesMayOverlap(baseType, field.className)
}

internal fun isAliasResultTypeCompatible(
    queryType: String,
    aliasType: String,
    typesMayOverlap: (String, String) -> Boolean,
): Boolean = queryType.replace('$', '.') == aliasType.replace('$', '.') ||
    typesMayOverlap(queryType, aliasType)
