package org.opentaint.dataflow.go.sequent

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.expr.GoIRBinOpExpr
import org.opentaint.ir.go.expr.GoIRMakeClosureExpr
import org.opentaint.ir.go.expr.GoIRNextExpr
import org.opentaint.ir.go.expr.GoIRTypeAssertExpr
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRFieldStore
import org.opentaint.ir.go.inst.GoIRGlobalStore
import org.opentaint.ir.go.inst.GoIRIndexStore
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.inst.GoIRMapUpdate
import org.opentaint.ir.go.inst.GoIRPhi
import org.opentaint.ir.go.inst.GoIRReturn
import org.opentaint.ir.go.inst.GoIRSend
import org.opentaint.ir.go.inst.GoIRStore
import org.opentaint.ir.go.type.GoIRBinaryOp
import org.opentaint.ir.go.value.GoIRValue

private data class Tmpl(
    val label: String,
    val before: FactSpec,
    val afters: List<FactSpec>,
    val roundTrip: Boolean = true,
    val exact: Boolean = true,
)

private fun spec(base: AccessPathBase, vararg accessors: Accessor) = FactSpec(base, accessors.toList())

private fun GoIRFunction.templatesFor(inst: GoIRInst): List<Tmpl> = when (inst) {
    is GoIRAssignInst -> assignTemplates(inst)
    is GoIRReturn -> returnTemplates(inst)
    is GoIRPhi -> phiTemplates(inst)
    is GoIRMapUpdate -> mapUpdateTemplates(inst)
    is GoIRSend -> sendTemplates(inst)
    is GoIRGlobalStore -> globalStoreTemplates(inst)
    is GoIRFieldStore -> fieldStoreTemplates(inst)
    is GoIRIndexStore -> indexStoreTemplates(inst)
    is GoIRStore -> ptrStoreTemplates(inst)
    else -> emptyList()
}

private fun GoIRFunction.baseOf(v: GoIRValue): AccessPathBase = GoFlowFunctionUtils.accessPathBase(v, this)

private fun GoIRFunction.assignTemplates(inst: GoIRAssignInst): List<Tmpl> {
    val reg = AccessPathBase.LocalVar(inst.register.index)
    val expr = inst.expr
    val tag = "${name}#${inst.register.index}"

    if (expr is GoIRBinOpExpr && expr.op == GoIRBinaryOp.ADD && GoFlowFunctionUtils.isStringType(expr.type)) {
        return listOf(expr.x, expr.y).mapIndexed { i, operand ->
            Tmpl("concat[$tag/${if (i == 0) "lhs" else "rhs"}]", spec(baseOf(operand)), listOf(spec(reg)))
        }
    }

    if (expr is GoIRTypeAssertExpr && expr.commaOk) {
        val slot0 = GoFlowFunctionUtils.tupleFieldAccessor(0)
        return listOf(Tmpl("commaOkAssert[$tag]", spec(baseOf(expr.x)), listOf(spec(reg, slot0))))
    }

    if (expr is GoIRMakeClosureExpr) {
        return expr.bindings.mapIndexed { i, binding ->
            val freeVar = GoFlowFunctionUtils.freeVarAccessor(expr.fn, i)
            Tmpl("makeClosure[$tag/bind$i]", spec(baseOf(binding)), listOf(spec(reg, freeVar)))
        }
    }

    if (expr is GoIRNextExpr) {
        val iter = baseOf(expr.iter)
        val slots = GoFlowFunctionUtils.rangeElementTupleSlots(expr, this)
        if (slots.isEmpty()) return emptyList()
        return listOf(Tmpl("next[$tag]", spec(iter, ElementAccessor), slots.map { spec(reg, it) }))
    }

    return when (val access = GoFlowFunctionUtils.exprToAccess(expr, this)) {
        is Access.Simple -> listOf(Tmpl("assignSimple[$tag]", spec(access.base), listOf(spec(reg))))
        is Access.RefAccess ->
            listOf(Tmpl("assignRef[$tag/${access.accessor.toSuffix()}]", spec(access.base, access.accessor), listOf(spec(reg))))
        null -> emptyList()
    }
}

private fun GoIRFunction.returnTemplates(inst: GoIRReturn): List<Tmpl> {
    if (inst.results.isEmpty()) return emptyList()
    if (inst.results.size == 1) {
        return listOf(Tmpl("return1[$name]", spec(baseOf(inst.results[0])), listOf(spec(AccessPathBase.Return))))
    }
    return inst.results.mapIndexed { i, rv ->
        val slot = GoFlowFunctionUtils.tupleFieldAccessor(i)
        Tmpl("returnN[$name/#$i]", spec(baseOf(rv)), listOf(spec(AccessPathBase.Return, slot)))
    }
}

private fun GoIRFunction.phiTemplates(inst: GoIRPhi): List<Tmpl> {
    val reg = AccessPathBase.LocalVar(inst.register.index)
    return inst.edges.values.mapIndexedNotNull { i, edge ->
        val base = baseOf(edge)
        if (base is AccessPathBase.Constant) null
        else Tmpl("phi[${name}#${inst.register.index}/edge$i]", spec(base), listOf(spec(reg)))
    }
}

private fun GoIRFunction.mapUpdateTemplates(inst: GoIRMapUpdate): List<Tmpl> {
    val map = baseOf(inst.map)
    val sources = listOf("value" to inst.value, "key" to inst.key)
    return sources.mapNotNull { (role, v) ->
        val base = baseOf(v)
        if (base is AccessPathBase.Constant) null
        else Tmpl("mapUpdate[$name/$role]", spec(base), listOf(spec(map, ElementAccessor)))
    }
}

private fun GoIRFunction.sendTemplates(inst: GoIRSend): List<Tmpl> {
    val chan = baseOf(inst.chan)
    return listOf(Tmpl("send[$name]", spec(baseOf(inst.x)), listOf(spec(chan, ElementAccessor))))
}

private fun GoIRFunction.globalStoreTemplates(inst: GoIRGlobalStore): List<Tmpl> {
    val access = GoFlowFunctionUtils.accessForGlobal(inst.global)
    return listOf(
        Tmpl(
            "globalStore[$name]", spec(baseOf(inst.value)),
            listOf(spec(access.base, access.accessor)), exact = false,
        )
    )
}

private fun GoIRFunction.fieldStoreTemplates(inst: GoIRFieldStore): List<Tmpl> {
    val instance = baseOf(inst.base)
    val field = GoFlowFunctionUtils.fieldAccessorFromStore(inst)
    return listOf(
        Tmpl("fieldStore[$name]", spec(baseOf(inst.value)), listOf(spec(instance, field)), exact = false)
    )
}

private fun GoIRFunction.indexStoreTemplates(inst: GoIRIndexStore): List<Tmpl> {
    val instance = baseOf(inst.base)
    return listOf(
        Tmpl("indexStore[$name]", spec(baseOf(inst.value)), listOf(spec(instance, ElementAccessor)), exact = false)
    )
}

private fun GoIRFunction.ptrStoreTemplates(inst: GoIRStore): List<Tmpl> {
    val dst = baseOf(inst.addr)
    return listOf(
        Tmpl("ptrStore[$name]", spec(baseOf(inst.value)), listOf(spec(dst)), exact = false)
    )
}

internal val TAILS: List<Pair<String, List<Accessor>>> = listOf(
    "plain" to emptyList(),
    "field" to listOf(org.opentaint.dataflow.ap.ifds.FieldAccessor("util.Tail", "g", "?")),
    "elem" to listOf(ElementAccessor),
    "mark" to listOf(org.opentaint.dataflow.ap.ifds.TaintMarkAccessor("taint")),
)

internal fun GoIRFunction.scenarios(): List<Scenario> {
    val instructions = body?.instructions ?: return emptyList()
    val out = mutableListOf<Scenario>()
    for (inst in instructions) {
        for (t in templatesFor(inst)) {
            if (t.before.base is AccessPathBase.Constant) continue
            for ((tailName, tail) in TAILS) {
                out += Scenario(
                    label = "${t.label}/$tailName",
                    inst = inst,
                    before = t.before.append(tail),
                    afters = t.afters.map { it.append(tail) },
                    roundTrip = t.roundTrip,
                    exact = t.exact,
                )
            }
        }
    }
    return out
}
