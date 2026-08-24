package org.opentaint.dataflow.python.util

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.ir.api.python.*

object PIRFlowFunctionUtils {

    fun accessPathBase(value: PIRValue): AccessPathBase? = when (value) {
        is PIRLocalVar -> AccessPathBase.LocalVar(value.index)
        is PIRParameterRef -> AccessPathBase.Argument(value.index)
        is PIRConst -> null
    }

    fun globalAccess(ref: PIRNameRef): Pair<AccessPathBase, Accessor> {
        val name = when (ref) {
            is PIRGlobalNameRef -> ref.qualifiedName
            is PIRModuleNameRef -> ref.module
        }
        return AccessPathBase.ClassStatic to ClassStaticAccessor(name)
    }

    fun implicitParamOffset(callee: PIRFunction): Int {
        if (callee.enclosingClass == null) return 0
        if (callee.isStaticMethod) return 0
        return 1
    }
}
