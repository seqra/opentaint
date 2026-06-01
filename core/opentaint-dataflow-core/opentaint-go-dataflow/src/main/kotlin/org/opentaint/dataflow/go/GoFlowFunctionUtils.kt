package org.opentaint.dataflow.go

import mu.KLogging
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
    ): AccessPathBase? {
        return when (value) {
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
            else -> {
                logger.error("Unsupported value type: ${value.javaClass.canonicalName}")
                null
            }
        }
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
                val base = accessPathBase(expr.x, method) ?: return null
                RefAccess(base, fieldAccessor(expr))
            }

            is GoIRFieldAddrExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                RefAccess(base, fieldAccessorFromAddr(expr))
            }

            is GoIRGlobalValueExpr -> accessForGlobal(expr.global)

            is GoIRFreeVarValueExpr -> accessForFreeVar(method, expr.freeVarIndex)

            // Index/element access
            is GoIRIndexExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                Access.RefAccess(base, ElementAccessor)
            }

            is GoIRIndexAddrExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                RefAccess(base, ElementAccessor)
            }

            is GoIRLookupExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
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
                    val base = accessPathBase(expr.x, method) ?: return null
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
                val base = accessPathBase(expr.tuple, method) ?: return null
                RefAccess(base, tupleFieldAccessor(expr.extractIndex, expr.type))
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

    private fun singleOperandAccess(value: GoIRValue, method: GoIRFunction): Access? {
        val base = accessPathBase(value, method) ?: return null
        return Simple(base)
    }

    /**
     * Resolves the access for a store destination address.
     * If the address was produced by FieldAddrExpr or IndexAddrExpr,
     * returns a RefAccess with the appropriate accessor.
     */
    fun accessForAddr(addr: GoIRValue, method: GoIRFunction): Access? {
        if (addr !is GoIRRegister) {
            return singleOperandAccess(addr, method)
        }
        val defInst = findDefInst(addr, method)
            ?: return Simple(AccessPathBase.LocalVar(addr.index))

        return when (val expr = (defInst as? GoIRAssignInst)?.expr) {
            is GoIRFieldAddrExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                RefAccess(base, fieldAccessorFromAddr(expr))
            }
            is GoIRIndexAddrExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                RefAccess(base, ElementAccessor)
            }
            else -> Simple(AccessPathBase.LocalVar(addr.index))
        }
    }

    /**
     * Walks a store-destination address back through nested address-of-field /
     * address-of-element producers to its root base, returning the root and the
     * accessor chain in LEAF-FIRST order (deepest field first).
     *
     * `*%5 = data` where %5 = &%4.v, %4 = &%3.n1, %3 = &%2.n1, %2 = &%1.n1
     * resolves to (LocalVar(1), [.v, .n1, .n1, .n1]).
     *
     * Returns null if `addr` is not a register-rooted field/element chain
     * (callers fall back to the single-level accessForAddr handling).
     */
    fun resolveAddrChain(addr: GoIRValue, method: GoIRFunction): Pair<AccessPathBase, List<Accessor>>? {
        if (addr !is GoIRRegister) return null
        val accessors = mutableListOf<Accessor>()
        var cur: GoIRValue = addr
        while (cur is GoIRRegister) {
            val expr = (findDefInst(cur, method) as? GoIRAssignInst)?.expr
            when (expr) {
                is GoIRFieldAddrExpr -> { accessors.add(fieldAccessorFromAddr(expr)); cur = expr.x }
                is GoIRIndexAddrExpr -> { accessors.add(ElementAccessor); cur = expr.x }
                else -> return AccessPathBase.LocalVar(cur.index) to accessors
            }
        }
        val base = accessPathBase(cur, method) ?: return null
        return base to accessors
    }

    // ── Field accessor helpers ───────────────────────────────────────

    fun tupleFieldAccessor(index: Int, elementType: GoIRType): FieldAccessor {
        return FieldAccessor("tuple", "\$$index", elementType.displayName)
    }

    fun freeVarAccessor(function: GoIRFunction, argSlot: Int): FieldAccessor {
        return FieldAccessor(function.fullName, "freeVar$$argSlot", "")
    }

    fun fieldAccessor(expr: GoIRFieldExpr): FieldAccessor {
        val structTypeName = resolveStructTypeName(expr.x.type)
        return FieldAccessor(structTypeName, expr.fieldName, expr.type.displayName)
    }

    fun fieldAccessorFromAddr(expr: GoIRFieldAddrExpr): FieldAccessor {
        val structTypeName = resolveStructTypeName(expr.x.type)
        return FieldAccessor(structTypeName, expr.fieldName, expr.type.displayName)
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

    private fun findDefInst(register: GoIRRegister, method: GoIRFunction): GoIRDefInst? {
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
        val defInst = findDefInst(register, method) ?: return null
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
        is PositionAccessor.FieldAccessor -> FieldAccessor(className, fieldName, fieldType)
    }

    fun detectGlobalReadName(inst: GoIRAssignInst): String? {
        val expr = inst.expr
        if (expr !is GoIRGlobalValueExpr) return null
        return expr.global.fullName
    }

    fun detectFieldReadName(inst: GoIRAssignInst, method: GoIRFunction): String? {
        val expr = inst.expr
        if (expr is GoIRFieldExpr) return expr.fieldName
        if (expr is GoIRUnOpExpr && expr.op == GoIRUnaryOp.DEREF) {
            val src = expr.x as? GoIRRegister ?: return null
            val srcDef = (findDefInst(src, method) as? GoIRAssignInst)?.expr
            if (srcDef is GoIRFieldAddrExpr) return srcDef.fieldName
            if (srcDef is GoIRFieldExpr) return srcDef.fieldName
        }
        return null
    }

    private val logger = object : KLogging() {}.logger
}
