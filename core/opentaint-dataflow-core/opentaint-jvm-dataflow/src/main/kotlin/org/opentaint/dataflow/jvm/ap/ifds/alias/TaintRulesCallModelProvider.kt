package org.opentaint.dataflow.jvm.ap.ifds.alias

import org.opentaint.dataflow.ap.ifds.analysis.alias.AAHeapAccessor
import org.opentaint.dataflow.configuration.jvm.Argument
import org.opentaint.dataflow.configuration.jvm.ClassStatic
import org.opentaint.dataflow.configuration.jvm.CopyAllMarks
import org.opentaint.dataflow.configuration.jvm.Position
import org.opentaint.dataflow.configuration.jvm.PositionAccessor
import org.opentaint.dataflow.configuration.jvm.PositionWithAccess
import org.opentaint.dataflow.configuration.jvm.Result
import org.opentaint.dataflow.configuration.jvm.This
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.alias.ExternalCallModelProvider.ExternalAssign
import org.opentaint.dataflow.jvm.ap.ifds.alias.ExternalCallModelProvider.ExternalObject
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.ir.api.jvm.JIRMethod

/**
 * The pass-through models of a method from the `CopyAllMarks` actions of the pass-through rules of
 * [modelProvider]. A position with a static base or with `AnyFieldAccessor` gives no model.
 * The DSU backend and the directed backend use the same models.
 */
internal class TaintRulesCallModelProvider(
    private val modelProvider: TaintRulesProvider?,
) : ExternalCallModelProvider {
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
        is PositionAccessor.FieldAccessor -> FieldAlias(
            AliasAccessor.Field(className, fieldName, fieldType),
            isImmutable = false
        )
    }
}
