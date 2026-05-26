package org.opentaint.dataflow.python

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.configuration.python.AllArguments
import org.opentaint.dataflow.configuration.python.Argument
import org.opentaint.dataflow.configuration.python.ClassRef
import org.opentaint.dataflow.configuration.python.KwArgument
import org.opentaint.dataflow.configuration.python.Position
import org.opentaint.dataflow.configuration.python.PositionAccessor
import org.opentaint.dataflow.configuration.python.PositionWithAccess
import org.opentaint.dataflow.configuration.python.Result
import org.opentaint.dataflow.configuration.python.This
import org.opentaint.dataflow.taint.PositionAccess

object PIRFlowFunctionUtils {
    fun Position.resolveAp() = resolveBaseAp()?.let { resolveAp(it) }

    fun Position.resolveAp(baseAp: AccessPathBase): PositionAccess? = when (this) {
        is KwArgument,
        is Argument,
        Result,
        This -> PositionAccess.Simple(baseAp)

        is ClassRef -> PositionAccess.Complex(
            PositionAccess.Simple(baseAp),
            ClassStaticAccessor(fqn)
        )

        is PositionWithAccess -> {
            val base = base.resolveAp(baseAp) ?: return null
            val accessor = access.resolve()
            PositionAccess.Complex(base, accessor)
        }

        AllArguments -> null // should be resolved during rule compilation
    }

    fun Position.resolveBaseAp(): AccessPathBase? = when (this) {
        is ClassRef -> AccessPathBase.ClassStatic
        is Argument -> AccessPathBase.Argument(index)
        Result -> AccessPathBase.Return
        This -> AccessPathBase.This
        is PositionWithAccess -> base.resolveBaseAp()

        is KwArgument,
        AllArguments -> null
    }

    private fun PositionAccessor.resolve(): Accessor = when (this) {
        PositionAccessor.ElementAccessor -> ElementAccessor
        is PositionAccessor.FieldAccessor -> FieldAccessor("", name, "")
    }

    val SELF_ACCESSOR = FieldAccessor("", "\$PIR_SELF", "")
}
