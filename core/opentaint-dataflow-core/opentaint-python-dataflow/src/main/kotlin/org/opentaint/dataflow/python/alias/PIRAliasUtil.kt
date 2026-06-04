package org.opentaint.dataflow.python.alias

import kotlinx.collections.immutable.PersistentList
import kotlinx.collections.immutable.persistentListOf
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.mkFieldAccessor
import org.opentaint.ir.api.python.PIRInstruction

/**
 * Consumer helpers mirroring the JVM `JIRAliasUtil`: expand a fact onto all
 * aliases of its (local-var) base. Accessors are minted name-only via the shared
 * [mkFieldAccessor] util, matching the engine's name-only attribute matching.
 */
fun PIRLocalAliasAnalysis.forEachAliasAfterStatement(
    statement: PIRInstruction,
    fact: FinalFactAp,
    body: (FinalFactAp) -> Unit,
) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    val aliases = findAliasAfterStatement(base, statement) ?: return
    aliases.filterNot { alias -> alias.base is AccessPathBase.Constant }
        .forEach { applyAlias(fact, it, body) }
}

fun PIRLocalAliasAnalysis.forEachHeapAliasAfterStatement(
    statement: PIRInstruction,
    fact: FinalFactAp,
    accessors: List<Accessor>,
    body: (FinalFactAp) -> Unit
) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    val aliasAccessors = accessors.map { it.aliasAccessor() ?: return }
    val child = accessors.fold(fact) { f, accessor ->
        f.readAccessor(accessor) ?: return
    }

    val aliases = findHeapAliasAfterStatement(base, aliasAccessors, statement) ?: return
    aliases.filterNot { alias -> alias.base is AccessPathBase.Constant }
        .forEach { alias -> applyAlias(child, alias, body) }
}

fun PIRLocalAliasAnalysis.forEachAliasAfterCallStatement(
    statement: PIRInstruction,
    fact: FinalFactAp,
    body: (FinalFactAp) -> Unit,
) {
    forEachAliasAfterStatement(statement, fact, body)

    collectCallFacts(fact).forEach { accessorList ->
        forEachHeapAliasAfterStatement(statement, fact, accessorList, body)
    }
}

private fun collectCallFacts(fact: FinalFactAp): List<List<Accessor>> {
    val accessorLists = mutableListOf<List<Accessor>>()
    collectCallFacts(fact, depth = 0, accessorLists = accessorLists, curList = persistentListOf())

    return accessorLists
}

private fun collectCallFacts(fact: FinalFactAp, depth: Int, accessorLists: MutableList<List<Accessor>>, curList: PersistentList<Accessor>) {
    if (depth > ACCESSOR_DEPTH) return

    fact.getStartAccessors().forEach { accessor ->
        val readFact = fact.readAccessor(accessor) ?: return@forEach
        val newList = curList.add(accessor)

        accessorLists += newList
        collectCallFacts(readFact, depth + 1, accessorLists, newList)
    }
}

private fun applyAlias(fact: FinalFactAp, alias: AliasApInfo, body: (FinalFactAp) -> Unit) {
    val result = alias.accessors.foldRight(fact.rebase(alias.base)) { accessor, f ->
        f.prependAccessor(accessor.apAccessor())
    }
    body(result)
}

fun AliasAccessor.apAccessor(): Accessor = when (this) {
    is AliasAccessor.Array -> ElementAccessor
    is AliasAccessor.Field -> mkFieldAccessor(name)
}

private fun Accessor.aliasAccessor(): AliasAccessor? = when (this) {
    is ElementAccessor -> AliasAccessor.Array
    is FieldAccessor -> AliasAccessor.Field(fieldName)
    else -> null
}

private const val ACCESSOR_DEPTH = 3
