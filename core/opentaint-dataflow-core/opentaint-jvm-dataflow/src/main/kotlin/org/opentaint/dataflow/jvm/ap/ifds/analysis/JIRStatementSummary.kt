package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary
import org.opentaint.dataflow.ap.ifds.summary.StatementSummaryBuilder
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.ir.api.jvm.cfg.JIRArrayAccess
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRBinaryExpr
import org.opentaint.ir.api.jvm.cfg.JIRCastExpr
import org.opentaint.ir.api.jvm.cfg.JIRExpr
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.ir.api.jvm.cfg.JIRValue

object JIRStatementSummary {
    fun build(apManager: ApManager, inst: JIRInst, aliasAnalysis: JIRLocalAliasAnalysis?): StatementSummary =
        builder(apManager, inst, aliasAnalysis, keepAliasPropagationEdges = false)?.build() ?: StatementSummary.Empty

    fun buildReversed(apManager: ApManager, inst: JIRInst, aliasAnalysis: JIRLocalAliasAnalysis?): StatementSummary =
        builder(apManager, inst, aliasAnalysis, keepAliasPropagationEdges = true)?.buildReversed() ?: StatementSummary.Empty

    private fun builder(
        apManager: ApManager,
        inst: JIRInst,
        aliasAnalysis: JIRLocalAliasAnalysis?,
        keepAliasPropagationEdges: Boolean,
    ): StatementSummaryBuilder? {
        val builder = StatementSummaryBuilder(apManager, keepAliasPropagationEdges)
        when (inst) {
            is JIRAssignInst -> builder.assign(inst, aliasAnalysis, inst.lhv, inst.rhv)
            is JIRReturnInst -> builder.move(AccessPathBase.Return, inst.returnValue?.let { valueBase(it) })
            is JIRThrowInst -> builder.move(AccessPathBase.Exception, valueBase(inst.throwable))
            else -> return null
        }
        return builder
    }

    private fun StatementSummaryBuilder.assign(
        inst: JIRInst,
        aliasAnalysis: JIRLocalAliasAnalysis?,
        lhv: JIRValue,
        rhv: JIRExpr,
    ) {
        if (rhv is JIRBinaryExpr) {
            assign(inst, aliasAnalysis, lhv, rhv.lhv)
            assign(inst, aliasAnalysis, lhv, rhv.rhv)
            return
        }

        val from = when (rhv) {
            is JIRCastExpr -> MethodFlowFunctionUtils.mkAccess(rhv.operand)?.also { filter(it.base, rhv.type) } ?: return
            is JIRImmediate -> MethodFlowFunctionUtils.mkAccess(rhv)?.also { filter(it.base, rhv.type) } ?: return
            is JIRArrayAccess -> MethodFlowFunctionUtils.mkAccess(rhv)?.also { filter(it.base, rhv.array.type) } ?: return
            is JIRFieldRef -> MethodFlowFunctionUtils.mkAccess(rhv)
                ?.also { filter(it.base, rhv.instance?.type) }
                ?.also { filter(it.base, rhv.field.enclosingType) }
                ?: return
            else -> null
        }

        val to = when (lhv) {
            is JIRImmediate -> MethodFlowFunctionUtils.mkAccess(lhv)?.also { filter(it.base, lhv.type) } ?: return
            is JIRArrayAccess -> MethodFlowFunctionUtils.mkAccess(lhv)?.also { filter(it.base, lhv.array.type) } ?: return
            is JIRFieldRef -> MethodFlowFunctionUtils.mkAccess(lhv)
                ?.also { filter(it.base, lhv.instance?.type) }
                ?.also { filter(it.base, lhv.field.enclosingType) }
                ?: return
            else -> error("Assign to complex value: $lhv")
        }

        val value = from?.base?.takeUnless { it is AccessPathBase.Constant }

        when {
            from is MethodFlowFunctionUtils.MemoryAccess -> {
                check(to !is MethodFlowFunctionUtils.MemoryAccess) { "Complex assignment: $lhv = $rhv" }
                read(to.base, from.base, path(from))
            }

            to is MethodFlowFunctionUtils.MemoryAccess -> {
                val accessors = path(to)
                write(
                    base = to.base,
                    accessors = accessors,
                    weak = accessors.first() is ElementAccessor,
                    values = listOfNotNull(value),
                    aliasPaths = aliasPaths(inst, aliasAnalysis, to.base),
                )
            }

            else -> move(to.base, value)
        }
    }

    private fun valueBase(value: JIRValue): AccessPathBase? =
        accessPathBase(value)?.takeUnless { it is AccessPathBase.Constant }

    private fun path(access: MethodFlowFunctionUtils.MemoryAccess): List<Accessor> = when (access) {
        is MethodFlowFunctionUtils.RefAccess -> listOf(access.accessor)
        is MethodFlowFunctionUtils.StaticRefAccess -> listOf(access.classStaticAccessor, access.accessor)
    }

    private fun aliasPaths(
        inst: JIRInst,
        aliasAnalysis: JIRLocalAliasAnalysis?,
        base: AccessPathBase,
    ): List<Pair<AccessPathBase, List<Accessor>>> {
        val paths = mutableListOf<Pair<AccessPathBase, List<Accessor>>>()
        aliasAnalysis?.forEachAliasPathAtStatement(inst, base) { aliasBase, aliasAccessors ->
            paths += aliasBase to aliasAccessors
        }
        return paths
    }
}
