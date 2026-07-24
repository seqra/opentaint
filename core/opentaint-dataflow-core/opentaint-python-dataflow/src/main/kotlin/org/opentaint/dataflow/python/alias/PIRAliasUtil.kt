package org.opentaint.dataflow.python.alias

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.alias.applyAlias
import org.opentaint.dataflow.ap.ifds.analysis.alias.forEachHeapAliasAfterStatement
import org.opentaint.dataflow.ap.ifds.analysis.alias.forEachHeapAliasBeforeStatement
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.mkFieldAccessor
import org.opentaint.ir.api.python.PIRInstruction

/**
 * Consumer helpers mirroring the JVM `JIRAliasUtil` / Go `GoAliasUtil`: expand a fact
 * onto all aliases of its (local-var) base. Accessors are minted name-only via the shared
 * [mkFieldAccessor] util, matching the engine's name-only attribute matching.
 *
 * Both before- and after-statement variants are provided (mirroring the shared base's
 * `findAlias` / `findAliasAfterStatement`). Flow functions read the before-statement state,
 * matching the Go backend which reads before uniformly at both sequent and call sites.
 */
fun PIRLocalAliasAnalysis.forEachAliasBeforeStatement(
    statement: PIRInstruction,
    fact: FinalFactAp,
    body: (FinalFactAp) -> Unit,
) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    val aliases = findAlias(base, statement) ?: return
    aliases.mapNotNull { it.relevantApInfo() }
        .forEach { applyAlias(fact, it, AliasAccessor::apAccessor, body) }
}

fun PIRLocalAliasAnalysis.forEachAliasBeforeCallStatement(
    statement: PIRInstruction,
    fact: FinalFactAp,
    body: (FinalFactAp) -> Unit,
) {
    forEachAliasBeforeStatement(statement, fact, body)
    forEachHeapAliasBeforeStatement(
        statement, fact, Accessor::aliasAccessor, AliasApInfo::relevantApInfo, AliasAccessor::apAccessor, body
    )
}

fun PIRLocalAliasAnalysis.forEachAliasAfterStatement(
    statement: PIRInstruction,
    fact: FinalFactAp,
    body: (FinalFactAp) -> Unit,
) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    val aliases = findAliasAfterStatement(base, statement) ?: return
    aliases.mapNotNull { it.relevantApInfo() }
        .forEach { applyAlias(fact, it, AliasAccessor::apAccessor, body) }
}

fun PIRLocalAliasAnalysis.forEachAliasAfterCallStatement(
    statement: PIRInstruction,
    fact: FinalFactAp,
    body: (FinalFactAp) -> Unit,
) {
    forEachAliasAfterStatement(statement, fact, body)
    forEachHeapAliasAfterStatement(
        statement, fact, Accessor::aliasAccessor, AliasApInfo::relevantApInfo, AliasAccessor::apAccessor, body
    )
}

private fun AliasApInfo.relevantApInfo(): AliasApInfo? =
    takeIf { it.base !is AccessPathBase.Constant }

fun AliasAccessor.apAccessor(): Accessor = when (this) {
    is AliasAccessor.Array -> ElementAccessor
    is AliasAccessor.Field -> mkFieldAccessor(name)
}

private fun Accessor.aliasAccessor(): AliasAccessor? = when (this) {
    is ElementAccessor -> AliasAccessor.Array
    is FieldAccessor -> AliasAccessor.Field(fieldName)
    else -> null
}
