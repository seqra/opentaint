package org.opentaint.dataflow.python.alias

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.mkFieldAccessor
import org.opentaint.ir.api.python.PIRInstruction

/**
 * Consumer helpers mirroring the JVM `JIRAliasUtil`: expand a fact onto all
 * aliases of its (local-var) base. Accessors are minted name-only via the shared
 * [mkFieldAccessor] util, matching the engine's name-only attribute matching.
 */
fun PIRLocalAliasAnalysis.forEachAliasAtStatement(
    statement: PIRInstruction,
    fact: FinalFactAp,
    body: (FinalFactAp) -> Unit,
) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    val aliases = findAlias(base, statement) ?: return
    aliases.forEach { applyAlias(fact, it, body) }
}

fun PIRLocalAliasAnalysis.forEachAliasAfterCallStatement(
    statement: PIRInstruction,
    fact: FinalFactAp,
    body: (FinalFactAp) -> Unit,
) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    val before = findAlias(base, statement) ?: return
    val after = findAliasAfterStatement(base, statement)?.toSet() ?: return
    before.filter { it in after }.forEach { applyAlias(fact, it, body) }
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
