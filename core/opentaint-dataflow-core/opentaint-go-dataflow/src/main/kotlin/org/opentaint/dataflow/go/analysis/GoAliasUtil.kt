package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.analysis.alias.AliasApInfoNoRef
import org.opentaint.dataflow.go.analysis.alias.GoAliasAccessor
import org.opentaint.dataflow.go.analysis.alias.GoAliasInfoNoRef
import org.opentaint.dataflow.go.analysis.alias.GoLocalAliasAnalysis
import org.opentaint.ir.go.inst.GoIRDefInst
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRRegister

fun GoLocalAliasAnalysis.forEachAliasAtStatement(statement: GoIRInst, fact: FinalFactAp, body: (FinalFactAp) -> Unit) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    val aliases = findAlias(base, statement) ?: return
    aliases.forEachRelevantAlias { alias -> applyAlias(fact, alias, body) }
}

fun GoLocalAliasAnalysis.forEachAliasAtStatement(statement: GoIRInst, fact: InitialFactAp, body: (InitialFactAp) -> Unit) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    val aliases = findAlias(base, statement) ?: return
    aliases.forEachRelevantAlias { alias -> applyAlias(fact, alias, body) }
}

fun GoLocalAliasAnalysis.forEachHeapAliasAtStatement(
    statement: GoIRInst,
    fact: FinalFactAp,
    accessor: Accessor,
    body: (FinalFactAp) -> Unit
) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    val goAliasAccessor = accessor.goAliasAccessor() ?: return
    val child = fact.readAccessor(accessor) ?: return

    val aliases = findHeapAlias(base, listOf(goAliasAccessor), statement) ?: return
    aliases.forEachRelevantAlias { alias -> applyAlias(child, alias, body) }
}

fun GoLocalAliasAnalysis.forEachPossibleAliasAtStatement(
    statement: GoIRInst,
    fact: InitialFactAp,
    body: (InitialFactAp) -> Unit
) {
    val bases = statement.localBases()
    forEachAliasAtStatementAmongBases(statement, fact, bases, body)
}

private fun GoLocalAliasAnalysis.forEachAliasAtStatementAmongBases(
    statement: GoIRInst,
    fact: InitialFactAp,
    bases: List<AccessPathBase.LocalVar>,
    body: (InitialFactAp) -> Unit
) {
    bases.forEach { base ->
        val aliases = findAlias(base, statement) ?: return@forEach
        aliases.forEachRelevantAlias { alias -> unapplyAlias(fact, base, alias, body) }
    }
}

private fun GoIRInst.localBases(): List<AccessPathBase.LocalVar> {
    val bases = mutableSetOf<AccessPathBase.LocalVar>()
    if (this is GoIRDefInst) bases += AccessPathBase.LocalVar(register.index)
    operands.forEach { operand ->
        if (operand is GoIRRegister) bases += AccessPathBase.LocalVar(operand.index)
    }
    return bases.toList()
}

private inline fun List<GoAliasInfoNoRef>.forEachRelevantAlias(body: (AliasApInfoNoRef) -> Unit) {
    filterIsInstance<AliasApInfoNoRef>()
        .filterNot { alias -> alias.base is AccessPathBase.Constant }
        .forEach { body(it) }
}

private fun applyAlias(fact: FinalFactAp, alias: AliasApInfoNoRef, body: (FinalFactAp) -> Unit) {
    val result = alias.accessors.foldRight(fact.rebase(alias.base)) { accessor, f ->
        val apAccessor = accessor.apAccessor()
        f.prependAccessor(apAccessor)
    }

    body(result)
}

private fun applyAlias(fact: InitialFactAp, alias: AliasApInfoNoRef, body: (InitialFactAp) -> Unit) {
    val result = alias.accessors.foldRight(fact.rebase(alias.base)) { accessor, f ->
        val apAccessor = accessor.apAccessor()
        f.prependAccessor(apAccessor)
    }

    body(result)
}

private fun unapplyAlias(
    fact: InitialFactAp,
    newBase: AccessPathBase,
    alias: AliasApInfoNoRef,
    body: (InitialFactAp) -> Unit
) {
    if (alias.base != fact.base) return

    val result = alias.accessors.fold(fact.rebase(newBase)) { f, accessor ->
        f.readAccessor(accessor.apAccessor()) ?: return
    }

    body(result)
}

private fun Accessor.goAliasAccessor(): GoAliasAccessor.NoRef? = when (this) {
    is ElementAccessor -> GoAliasAccessor.Array
    is FieldAccessor -> GoAliasAccessor.Field(className, fieldName)
    else -> null
}

private fun GoAliasAccessor.NoRef.apAccessor(): Accessor = when (this) {
    is GoAliasAccessor.Array -> ElementAccessor
    is GoAliasAccessor.Field -> GoFlowFunctionUtils.createFieldAccessor(className, fieldName)
    is GoAliasAccessor.Global -> ClassStaticAccessor(name)
}
