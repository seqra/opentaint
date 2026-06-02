package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.analysis.alias.AliasApInfoNoRef
import org.opentaint.dataflow.go.analysis.alias.GoAliasAccessor
import org.opentaint.dataflow.go.analysis.alias.GoLocalAliasAnalysis
import org.opentaint.ir.go.inst.GoIRInst

fun GoLocalAliasAnalysis.forEachAliasAtStatement(statement: GoIRInst, fact: FinalFactAp, body: (FinalFactAp) -> Unit) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    val aliases = findAlias(base, statement) ?: return
    aliases.filterIsInstance<AliasApInfoNoRef>()
        .filterNot { alias -> alias.base is AccessPathBase.Constant }
        .forEach { alias -> applyAlias(fact, alias, body) }
}

private fun applyAlias(fact: FinalFactAp, alias: AliasApInfoNoRef, body: (FinalFactAp) -> Unit) {
    val result = alias.accessors.foldRight(fact.rebase(alias.base)) { accessor, f ->
        val apAccessor = accessor.apAccessor()
        f.prependAccessor(apAccessor)
    }

    body(result)
}

private fun GoAliasAccessor.NoRef.apAccessor(): Accessor = when (this) {
    is GoAliasAccessor.Array -> ElementAccessor
    is GoAliasAccessor.Field -> GoFlowFunctionUtils.createFieldAccessor(className, fieldName)
}
