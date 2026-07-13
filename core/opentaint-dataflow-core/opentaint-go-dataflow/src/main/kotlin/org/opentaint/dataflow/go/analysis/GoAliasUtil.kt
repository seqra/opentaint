package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.alias.forEachAliasAtStatement
import org.opentaint.dataflow.ap.ifds.analysis.alias.forEachAliasAtStatementAmongBases
import org.opentaint.dataflow.ap.ifds.analysis.alias.forEachHeapAliasBeforeStatement
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.analysis.alias.AliasApInfoNoRef
import org.opentaint.dataflow.go.analysis.alias.GoAliasAccessor
import org.opentaint.dataflow.go.analysis.alias.GoAliasInfoNoRef
import org.opentaint.dataflow.go.analysis.alias.GoLocalAliasAnalysis
import org.opentaint.ir.go.inst.GoIRDefInst
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRRegister

fun GoLocalAliasAnalysis.forEachAliasAtStatement(statement: GoIRInst, fact: FinalFactAp, body: (FinalFactAp) -> Unit) =
    forEachAliasAtStatement(statement, fact, GoAliasInfoNoRef::relevantApInfo, GoAliasAccessor.NoRef::apAccessor, body)

fun GoLocalAliasAnalysis.forEachAliasAtStatement(statement: GoIRInst, fact: InitialFactAp, body: (InitialFactAp) -> Unit) =
    forEachAliasAtStatement(statement, fact, GoAliasInfoNoRef::relevantApInfo, GoAliasAccessor.NoRef::apAccessor, body)

fun GoLocalAliasAnalysis.forEachHeapAliasAtStatement(
    statement: GoIRInst,
    fact: FinalFactAp,
    body: (FinalFactAp) -> Unit
) = forEachHeapAliasBeforeStatement(
    statement, fact, Accessor::goAliasAccessor, GoAliasInfoNoRef::relevantApInfo, GoAliasAccessor.NoRef::apAccessor, body
)

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
) = forEachAliasAtStatementAmongBases(statement, fact, bases, GoAliasInfoNoRef::relevantApInfo, GoAliasAccessor.NoRef::apAccessor, body)

private fun GoIRInst.localBases(): List<AccessPathBase.LocalVar> {
    val bases = mutableSetOf<AccessPathBase.LocalVar>()
    if (this is GoIRDefInst) bases += AccessPathBase.LocalVar(register.index)
    operands.forEach { operand ->
        if (operand is GoIRRegister) bases += AccessPathBase.LocalVar(operand.index)
    }
    return bases.toList()
}

private fun GoAliasInfoNoRef.relevantApInfo(): AliasApInfoNoRef? =
    (this as? AliasApInfoNoRef)?.takeIf { it.base !is AccessPathBase.Constant }

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
