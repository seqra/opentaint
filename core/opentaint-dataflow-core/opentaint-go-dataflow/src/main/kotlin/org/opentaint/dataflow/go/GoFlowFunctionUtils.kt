package org.opentaint.dataflow.go

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access.RefAccess
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access.Simple
import org.opentaint.dataflow.go.rules.Position
import org.opentaint.dataflow.go.rules.PositionAccessor
import org.opentaint.dataflow.go.rules.PositionWithAccess
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRGlobal
import org.opentaint.ir.go.cfg.GoIRCallInfo
import org.opentaint.ir.go.expr.GoIRAllocExpr
import org.opentaint.ir.go.expr.GoIRBinOpExpr
import org.opentaint.ir.go.expr.GoIRBuiltinValueExpr
import org.opentaint.ir.go.expr.GoIRChangeInterfaceExpr
import org.opentaint.ir.go.expr.GoIRChangeTypeExpr
import org.opentaint.ir.go.expr.GoIRConvertExpr
import org.opentaint.ir.go.expr.GoIRExpr
import org.opentaint.ir.go.expr.GoIRExtractExpr
import org.opentaint.ir.go.expr.GoIRFieldAddrExpr
import org.opentaint.ir.go.expr.GoIRFieldExpr
import org.opentaint.ir.go.expr.GoIRFreeVarValueExpr
import org.opentaint.ir.go.expr.GoIRFunctionValueExpr
import org.opentaint.ir.go.expr.GoIRGlobalValueExpr
import org.opentaint.ir.go.expr.GoIRIndexAddrExpr
import org.opentaint.ir.go.expr.GoIRIndexExpr
import org.opentaint.ir.go.expr.GoIRLookupExpr
import org.opentaint.ir.go.expr.GoIRMakeChanExpr
import org.opentaint.ir.go.expr.GoIRMakeClosureExpr
import org.opentaint.ir.go.expr.GoIRMakeInterfaceExpr
import org.opentaint.ir.go.expr.GoIRMakeMapExpr
import org.opentaint.ir.go.expr.GoIRMakeSliceExpr
import org.opentaint.ir.go.expr.GoIRMultiConvertExpr
import org.opentaint.ir.go.expr.GoIRNextExpr
import org.opentaint.ir.go.expr.GoIRRangeExpr
import org.opentaint.ir.go.expr.GoIRSelectExpr
import org.opentaint.ir.go.expr.GoIRSliceExpr
import org.opentaint.ir.go.expr.GoIRSliceToArrayPointerExpr
import org.opentaint.ir.go.expr.GoIRTypeAssertExpr
import org.opentaint.ir.go.expr.GoIRUnOpExpr
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRCall
import org.opentaint.ir.go.inst.GoIRDefInst
import org.opentaint.ir.go.inst.GoIRDefer
import org.opentaint.ir.go.inst.GoIRFieldStore
import org.opentaint.ir.go.inst.GoIRGo
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.type.GoIRArrayType
import org.opentaint.ir.go.type.GoIRBasicType
import org.opentaint.ir.go.type.GoIRBasicTypeKind
import org.opentaint.ir.go.type.GoIRBinaryOp
import org.opentaint.ir.go.type.GoIRMapType
import org.opentaint.ir.go.type.GoIRNamedTypeRef
import org.opentaint.ir.go.type.GoIRPointerType
import org.opentaint.ir.go.type.GoIRSliceType
import org.opentaint.ir.go.type.GoIRStructType
import org.opentaint.ir.go.type.GoIRType
import org.opentaint.ir.go.type.GoIRUnaryOp
import org.opentaint.ir.go.value.GoIRConstValue
import org.opentaint.ir.go.value.GoIRParameterValue
import org.opentaint.ir.go.value.GoIRRegister
import org.opentaint.ir.go.value.GoIRValue

object GoFlowFunctionUtils {
    sealed interface Access {
        val base: AccessPathBase

        data class Simple(override val base: AccessPathBase) : Access
        data class RefAccess(
            override val base: AccessPathBase,
            val accessor: Accessor,
        ) : Access
    }

    fun accessPathBase(
        value: GoIRValue,
        method: GoIRFunction?
    ): AccessPathBase = when (value) {
        is GoIRParameterValue -> {
            if (method != null && method.isMethod && value.paramIndex == 0) {
                AccessPathBase.This
            } else {
                val shift = if (method != null && method.isMethod) 1 else 0
                AccessPathBase.Argument(value.paramIndex - shift)
            }
        }

        is GoIRRegister -> AccessPathBase.LocalVar(value.index)
        is GoIRConstValue -> AccessPathBase.Constant(value.type.displayName, value.value.toString())
        else -> error("Unexpected value: $value")
    }

    fun accessForGlobal(global: GoIRGlobal) = RefAccess(
        AccessPathBase.ClassStatic,
        ClassStaticAccessor(global.fullName)
    )

    fun accessForFreeVar(method: GoIRFunction, varIdx: Int): Access = RefAccess(
        AccessPathBase.This,
        freeVarAccessor(method, varIdx)
    )

    fun exprToAccess(expr: GoIRExpr, method: GoIRFunction): Access? {
        return when (expr) {
            // Field access
            is GoIRFieldExpr -> {
                val base = accessPathBase(expr.x, method)
                RefAccess(base, fieldAccessor(expr))
            }

            is GoIRFieldAddrExpr -> {
                val base = accessPathBase(expr.x, method)
                RefAccess(base, fieldAccessorFromAddr(expr))
            }

            is GoIRGlobalValueExpr -> accessForGlobal(expr.global)

            is GoIRFreeVarValueExpr -> accessForFreeVar(method, expr.freeVarIndex)

            // Index/element access
            is GoIRIndexExpr -> {
                val base = accessPathBase(expr.x, method)
                RefAccess(base, ElementAccessor)
            }

            is GoIRIndexAddrExpr -> {
                val base = accessPathBase(expr.x, method)
                RefAccess(base, ElementAccessor)
            }

            is GoIRLookupExpr -> {
                val base = accessPathBase(expr.x, method)
                RefAccess(base, ElementAccessor)
            }

            // Conversions/wrapping (preserve taint)
            is GoIRChangeTypeExpr -> singleOperandAccess(expr.x, method)
            is GoIRConvertExpr -> singleOperandAccess(expr.x, method)
            is GoIRMultiConvertExpr -> singleOperandAccess(expr.x, method)
            is GoIRChangeInterfaceExpr -> singleOperandAccess(expr.x, method)
            is GoIRMakeInterfaceExpr -> singleOperandAccess(expr.x, method)
            is GoIRTypeAssertExpr -> singleOperandAccess(expr.x, method)
            is GoIRSliceToArrayPointerExpr -> singleOperandAccess(expr.x, method)

            // Pointer ops
            is GoIRUnOpExpr -> when (expr.op) {
                GoIRUnaryOp.DEREF -> singleOperandAccess(expr.x, method)
                GoIRUnaryOp.ARROW -> {
                    // Channel receive: <-ch reads element from channel
                    val base = accessPathBase(expr.x, method)
                    RefAccess(base, ElementAccessor)
                }
                else -> null // NOT, NEG, XOR — kills taint
            }

            // Slice (sub-view preserves taint)
            is GoIRSliceExpr -> singleOperandAccess(expr.x, method)

            // Range iteration
            is GoIRRangeExpr -> singleOperandAccess(expr.x, method)
            is GoIRNextExpr -> singleOperandAccess(expr.iter, method)

            // Tuple extract (multi-return): index-sensitive
            is GoIRExtractExpr -> {
                val base = accessPathBase(expr.tuple, method)
                RefAccess(base, tupleFieldAccessor(expr.extractIndex))
            }

            // Binary op: string concat preserves taint, arithmetic doesn't
            is GoIRBinOpExpr -> {
                if (expr.op == GoIRBinaryOp.ADD && isStringType(expr.type)) {
                    singleOperandAccess(expr.x, method)
                } else {
                    null
                }
            }

            // Allocations: no taint source
            is GoIRAllocExpr -> null
            is GoIRMakeSliceExpr -> null
            is GoIRMakeMapExpr -> null
            is GoIRMakeChanExpr -> null

            // Closure: taint if any binding is tainted
            is GoIRMakeClosureExpr -> {
                if (expr.bindings.isNotEmpty()) {
                    singleOperandAccess(expr.bindings.first(), method)
                } else {
                    null
                }
            }

            // Select: complex, treat as opaque
            is GoIRSelectExpr -> null
            is GoIRBuiltinValueExpr -> null
            is GoIRFunctionValueExpr -> null
        }
    }

    private fun singleOperandAccess(value: GoIRValue, method: GoIRFunction): Access {
        val base = accessPathBase(value, method)
        return Simple(base)
    }

    fun tupleFieldAccessor(index: Int): FieldAccessor {
        return createFieldAccessor("tuple", "\$$index")
    }

    fun rangeElementTupleSlots(expr: GoIRNextExpr, method: GoIRFunction): List<FieldAccessor> {
        val collectionType = rangedCollectionType(expr, method) ?: return emptyList()
        return when (resolveUnderlyingType(collectionType)) {
            is GoIRMapType -> listOf(tupleFieldAccessor(1), tupleFieldAccessor(2))
            is GoIRSliceType -> listOf(tupleFieldAccessor(2))
            is GoIRArrayType -> listOf(tupleFieldAccessor(2))
            else -> emptyList()
        }
    }

    private fun rangedCollectionType(expr: GoIRNextExpr, method: GoIRFunction): GoIRType? {
        val iter = expr.iter as? GoIRRegister ?: return null
        val rangeExpr = (findDefInstUnsafe(iter, method) as? GoIRAssignInst)?.expr as? GoIRRangeExpr ?: return null
        return rangeExpr.x.type
    }

    private fun resolveUnderlyingType(type: GoIRType): GoIRType = when (type) {
        is GoIRNamedTypeRef -> resolveUnderlyingType(type.namedType.underlying)
        is GoIRPointerType -> resolveUnderlyingType(type.elem)
        else -> type
    }

    fun freeVarAccessor(function: GoIRFunction, argSlot: Int): FieldAccessor {
        return createFieldAccessor(function.fullName, "freeVar$$argSlot")
    }

    fun fieldAccessor(expr: GoIRFieldExpr): FieldAccessor {
        val structTypeName = resolveStructTypeName(expr.x.type)
        return createFieldAccessor(structTypeName, expr.fieldName)
    }

    fun fieldAccessorFromAddr(expr: GoIRFieldAddrExpr): FieldAccessor {
        val structTypeName = resolveStructTypeName(expr.x.type)
        return createFieldAccessor(structTypeName, expr.fieldName)
    }

    fun fieldAccessorFromStore(inst: GoIRFieldStore): FieldAccessor {
        val structTypeName = resolveStructTypeName(inst.base.type)
        return createFieldAccessor(structTypeName, inst.fieldName)
    }

    private fun resolveStructTypeName(type: GoIRType): String {
        return when (type) {
            is GoIRNamedTypeRef -> type.namedType.fullName
            is GoIRPointerType -> resolveStructTypeName(type.elem)
            is GoIRStructType -> type.namedType?.fullName ?: "anonymous"
            else -> type.displayName
        }
    }

    // ── Defining instruction lookup ──────────────────────────────────

    private fun findDefInstUnsafe(register: GoIRRegister, method: GoIRFunction): GoIRDefInst? {
        val body = method.body ?: return null
        val instAtIdx = body.instructions.getOrNull(register.index) as? GoIRDefInst
        if (instAtIdx != null && instAtIdx.register == register) return instAtIdx

        return body.instructions
            .filterIsInstance<GoIRDefInst>()
            .firstOrNull { it.register == register }
    }

    /**
     * Traces a register back to a MakeClosureExpr, if it was defined by one.
     */
    fun findMakeClosureExpr(register: GoIRRegister, method: GoIRFunction): GoIRMakeClosureExpr? {
        val defInst = findDefInstUnsafe(register, method) ?: return null
        return (defInst as? GoIRAssignInst)?.expr as? GoIRMakeClosureExpr
    }

    // ── Call info extraction ─────────────────────────────────────────

    fun extractCallInfo(inst: GoIRInst): GoIRCallInfo? {
        return when (inst) {
            is GoIRCall -> inst.call
            is GoIRGo -> inst.call
            is GoIRDefer -> inst.call
            else -> null
        }
    }

    fun extractResultRegister(inst: GoIRInst): GoIRRegister? {
        return when (inst) {
            is GoIRCall -> inst.register
            else -> null
        }
    }

    fun isStringType(type: GoIRType): Boolean {
        return type is GoIRBasicType && type.kind == GoIRBasicTypeKind.STRING
    }

    fun Position.resolvePosAccess(): PositionAccess = when (this) {
        is Position.Simple -> resolvePosAccess()
        is PositionWithAccess -> PositionAccess.Complex(base.resolvePosAccess(), access.resolvePosAccess())
    }

    fun Position.Simple.resolvePosAccess(): PositionAccess.Simple {
        val base = when (this) {
            is Position.Argument -> AccessPathBase.Argument(index)
            is Position.Result -> AccessPathBase.Return
            is Position.This -> AccessPathBase.This
        }
        return PositionAccess.Simple(base)
    }

    fun PositionAccessor.resolvePosAccess(): Accessor = when (this) {
        is PositionAccessor.ElementAccessor -> ElementAccessor
        is PositionAccessor.FieldAccessor -> createFieldAccessor(className, fieldName)
    }

    fun detectGlobalReadName(inst: GoIRAssignInst): String? {
        val expr = inst.expr
        if (expr !is GoIRGlobalValueExpr) return null
        return expr.global.fullName
    }

    fun detectFieldReadName(inst: GoIRAssignInst): String? {
        val expr = inst.expr
        if (expr is GoIRFieldExpr) return expr.fieldName
        if (expr is GoIRFieldAddrExpr) return expr.fieldName
        return null
    }

    fun createFieldAccessor(struct: String, fieldName: String): FieldAccessor =
        FieldAccessor(struct, fieldName, "?")
}
