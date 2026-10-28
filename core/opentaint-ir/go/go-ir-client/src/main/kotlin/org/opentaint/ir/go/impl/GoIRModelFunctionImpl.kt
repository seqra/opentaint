package org.opentaint.ir.go.impl

import org.opentaint.ir.go.api.GoIRApproximatedFunction
import org.opentaint.ir.go.api.GoIRFreeVar
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRModelFunction
import org.opentaint.ir.go.api.GoIRPackage
import org.opentaint.ir.go.api.GoIRParameter
import org.opentaint.ir.go.api.GoIRPosition
import org.opentaint.ir.go.api.GoIRTypeParamDecl
import org.opentaint.ir.go.api.GoIrFunctionReference
import org.opentaint.ir.go.type.GoIRFuncType
import org.opentaint.ir.go.type.GoIRType

open class GoIRModelFunctionImpl(
    name: String,
    fullName: String,
    pkg: GoIRPackage?,
    signature: GoIRFuncType,
    params: List<GoIRParameter>,
    freeVars: List<GoIRFreeVar>,
    position: GoIRPosition?,
    isMethod: Boolean,
    isPointerReceiver: Boolean,
    isExported: Boolean,
    syntheticKind: String?,
    declaredHasBody: Boolean,
    parent: GoIrFunctionReference?,
    anonymousFunctions: List<GoIrFunctionReference>,
    typeParams: List<GoIRTypeParamDecl>,
    originFullName: String?,
    typeArgs: List<GoIRType>,
) : GoIRFunctionImpl(
    name, fullName, pkg, signature, params, freeVars, position, isMethod, isPointerReceiver, isExported,
    isSynthetic = true, syntheticKind, declaredHasBody, parent, anonymousFunctions, typeParams, originFullName, typeArgs,
), GoIRModelFunction {
    override fun toString(): String = "GoIRModelFunction($fullName)"
}

class GoIRApproximatedFunctionImpl(
    override val original: GoIRFunction,
    name: String,
    fullName: String,
    pkg: GoIRPackage?,
    signature: GoIRFuncType,
    params: List<GoIRParameter>,
    freeVars: List<GoIRFreeVar>,
    position: GoIRPosition?,
    isMethod: Boolean,
    isPointerReceiver: Boolean,
    isExported: Boolean,
    syntheticKind: String?,
    declaredHasBody: Boolean,
    parent: GoIrFunctionReference?,
    anonymousFunctions: List<GoIrFunctionReference>,
    typeParams: List<GoIRTypeParamDecl>,
    originFullName: String?,
    typeArgs: List<GoIRType>,
) : GoIRModelFunctionImpl(
    name, fullName, pkg, signature, params, freeVars, position, isMethod, isPointerReceiver, isExported,
    syntheticKind, declaredHasBody, parent, anonymousFunctions, typeParams, originFullName, typeArgs,
), GoIRApproximatedFunction
