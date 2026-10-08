package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary
import org.opentaint.dataflow.ap.ifds.summary.StatementSummaryBuilder
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access
import org.opentaint.dataflow.go.analysis.alias.GoLocalAliasAnalysis
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.expr.GoIRBinOpExpr
import org.opentaint.ir.go.expr.GoIRExpr
import org.opentaint.ir.go.expr.GoIRLookupExpr
import org.opentaint.ir.go.expr.GoIRMakeClosureExpr
import org.opentaint.ir.go.expr.GoIRNextExpr
import org.opentaint.ir.go.expr.GoIRTypeAssertExpr
import org.opentaint.ir.go.expr.GoIRUnOpExpr
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

object GoStatementSummary {
    fun build(
        apManager: ApManager,
        inst: GoIRInst,
        method: GoIRFunction,
        aliasAnalysis: GoLocalAliasAnalysis,
    ): StatementSummary =
        builder(apManager, inst, method, aliasAnalysis, keepAliasPropagationEdges = false)?.build()
            ?: StatementSummary.Empty

    fun buildReversed(
        apManager: ApManager,
        inst: GoIRInst,
        method: GoIRFunction,
        aliasAnalysis: GoLocalAliasAnalysis,
    ): StatementSummary =
        builder(apManager, inst, method, aliasAnalysis, keepAliasPropagationEdges = true)?.buildReversed()
            ?: StatementSummary.Empty

    private fun builder(
        apManager: ApManager,
        inst: GoIRInst,
        method: GoIRFunction,
        aliasAnalysis: GoLocalAliasAnalysis,
        keepAliasPropagationEdges: Boolean,
    ): StatementSummaryBuilder? {
        val builder = StatementSummaryBuilder(apManager, keepAliasPropagationEdges)
        val translator = Translator(builder, inst, method, aliasAnalysis)
        when (inst) {
            is GoIRAssignInst -> translator.assign(AccessPathBase.LocalVar(inst.register.index), inst.expr)
            is GoIRPhi -> translator.phi(inst)
            is GoIRStore -> translator.write(inst.addr, emptyList(), weak = false, listOf(inst.value))
            is GoIRFieldStore -> translator.write(
                inst.base, listOf(GoFlowFunctionUtils.fieldAccessorFromStore(inst)), weak = false, listOf(inst.value)
            )
            is GoIRIndexStore -> translator.write(inst.base, listOf(ElementAccessor), weak = true, listOf(inst.value))
            is GoIRGlobalStore -> translator.globalStore(inst)
            is GoIRMapUpdate -> translator.write(inst.map, listOf(ElementAccessor), weak = true, listOf(inst.value, inst.key))
            is GoIRSend -> translator.write(inst.chan, listOf(ElementAccessor), weak = true, listOf(inst.x))
            is GoIRReturn -> translator.ret(inst)
            else -> return null
        }
        return builder
    }

    private class Translator(
        private val builder: StatementSummaryBuilder,
        private val inst: GoIRInst,
        private val method: GoIRFunction,
        private val aliasAnalysis: GoLocalAliasAnalysis,
    ) {
        private fun base(value: GoIRValue): AccessPathBase = GoFlowFunctionUtils.accessPathBase(value, method)

        fun assign(to: AccessPathBase, expr: GoIRExpr) {
            when {
                expr.isCommaOk() -> assignAccess(
                    to, GoFlowFunctionUtils.exprToAccess(expr, method), listOf(GoFlowFunctionUtils.tupleFieldAccessor(0))
                )

                expr is GoIRBinOpExpr && expr.op == GoIRBinaryOp.ADD && GoFlowFunctionUtils.isStringType(expr.type) -> {
                    builder.move(to, base(expr.x))
                    builder.move(to, base(expr.y))
                }

                expr is GoIRMakeClosureExpr -> {
                    builder.touch(to)
                    for ((i, binding) in expr.bindings.withIndex()) {
                        builder.move(to, base(binding), listOf(GoFlowFunctionUtils.freeVarAccessor(expr.fn, i)))
                    }
                }

                expr is GoIRNextExpr -> builder.read(
                    to, base(expr.iter), listOf(ElementAccessor),
                    GoFlowFunctionUtils.rangeElementTupleSlots(expr, method).map { listOf(it) },
                )

                else -> assignAccess(to, GoFlowFunctionUtils.exprToAccess(expr, method), emptyList())
            }
        }

        private fun assignAccess(to: AccessPathBase, access: Access?, toAccessors: List<Accessor>) {
            when (access) {
                null -> builder.touch(to)
                is Access.Simple -> builder.move(to, access.base, toAccessors)
                is Access.RefAccess -> builder.read(to, access.base, listOf(access.accessor), listOf(toAccessors))
            }
        }

        fun phi(phi: GoIRPhi) {
            val to = AccessPathBase.LocalVar(phi.register.index)
            for (value in phi.edges.values) {
                builder.move(to, base(value))
            }
        }

        fun ret(ret: GoIRReturn) {
            val single = ret.results.size == 1
            for ((i, value) in ret.results.withIndex()) {
                val accessors = if (single) emptyList() else listOf(GoFlowFunctionUtils.tupleFieldAccessor(i))
                builder.move(AccessPathBase.Return, base(value), accessors)
            }
        }

        fun write(target: GoIRValue, accessors: List<Accessor>, weak: Boolean, values: List<GoIRValue>) {
            val targetBase = base(target)
            builder.write(targetBase, accessors, weak, values.map { base(it) }.distinct(), aliasPaths(targetBase))
        }

        fun globalStore(store: GoIRGlobalStore) {
            val access = GoFlowFunctionUtils.accessForGlobal(store.global)
            builder.write(access.base, listOf(access.accessor), weak = false, listOf(base(store.value)), emptyList())
        }

        private fun aliasPaths(base: AccessPathBase): List<Pair<AccessPathBase, List<Accessor>>> {
            val paths = mutableListOf<Pair<AccessPathBase, List<Accessor>>>()
            aliasAnalysis.forEachAliasPathAtStatement(inst, base) { aliasBase, aliasAccessors ->
                paths += aliasBase to aliasAccessors
            }
            return paths
        }

        private fun GoIRExpr.isCommaOk(): Boolean = when (this) {
            is GoIRLookupExpr -> commaOk
            is GoIRTypeAssertExpr -> commaOk
            is GoIRUnOpExpr -> commaOk
            else -> false
        }
    }
}
