package org.opentaint.dataflow.go

import mu.KLogging
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.go.rules.Position
import org.opentaint.dataflow.go.rules.PositionAccessor
import org.opentaint.dataflow.go.rules.PositionWithAccess
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.cfg.GoIRCallInfo
import org.opentaint.ir.go.expr.GoIRAllocExpr
import org.opentaint.ir.go.expr.GoIRBinOpExpr
import org.opentaint.ir.go.expr.GoIRChangeInterfaceExpr
import org.opentaint.ir.go.expr.GoIRChangeTypeExpr
import org.opentaint.ir.go.expr.GoIRConvertExpr
import org.opentaint.ir.go.expr.GoIRExpr
import org.opentaint.ir.go.expr.GoIRExtractExpr
import org.opentaint.ir.go.expr.GoIRFieldAddrExpr
import org.opentaint.ir.go.expr.GoIRFieldExpr
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
import org.opentaint.ir.go.type.GoIRBasicType
import org.opentaint.ir.go.type.GoIRBasicTypeKind
import org.opentaint.ir.go.type.GoIRBinaryOp
import org.opentaint.ir.go.type.GoIRNamedTypeRef
import org.opentaint.ir.go.type.GoIRPointerType
import org.opentaint.ir.go.type.GoIRStructType
import org.opentaint.ir.go.type.GoIRType
import org.opentaint.ir.go.type.GoIRUnaryOp
import org.opentaint.ir.go.value.GoIRBuiltinValue
import org.opentaint.ir.go.value.GoIRConstValue
import org.opentaint.ir.go.value.GoIRFreeVarValue
import org.opentaint.ir.go.value.GoIRFunctionValue
import org.opentaint.ir.go.value.GoIRGlobalValue
import org.opentaint.ir.go.value.GoIRParameterValue
import org.opentaint.ir.go.value.GoIRRegister
import org.opentaint.ir.go.value.GoIRValue
import java.util.concurrent.atomic.AtomicBoolean

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
        method: GoIRFunction?,
    ): AccessPathBase? = accessPathBase(value, method) {
        if (globalsNotSupportedReported.compareAndSet(false, true)) {
            logger.error("TODO: Global values are not supported")
        }
        return null
    }

    private inline fun accessPathBase(
        value: GoIRValue,
        method: GoIRFunction?,
        handleGlobal: (GoIRGlobalValue) -> Nothing
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
            is GoIRGlobalValue -> handleGlobal(value)
            is GoIRFunctionValue -> AccessPathBase.Constant("func", value.function.fullName)
            is GoIRBuiltinValue -> AccessPathBase.Constant("builtin", value.name)
            is GoIRFreeVarValue -> {
                if (method == null) return null
                val paramCount = nonReceiverParamCount(method)
                AccessPathBase.Argument(paramCount + value.freeVarIndex)
            }
            else -> {
                logger.error("Unsupported value type: ${value.javaClass.canonicalName}")
                null
            }
        }
    }

    /**
     * Number of *non-receiver* parameters of a Go function.
     * For methods, the IR includes the receiver as `params[0]`, so we subtract 1.
     * For non-method functions, every entry in `params` is an explicit arg.
     */
    fun nonReceiverParamCount(method: GoIRFunction): Int =
        if (method.isMethod) method.params.size - 1 else method.params.size

    fun exprToAccess(expr: GoIRExpr, method: GoIRFunction): Access? {
        return when (expr) {
            // Field access
            is GoIRFieldExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                Access.RefAccess(base, fieldAccessor(expr))
            }
            is GoIRFieldAddrExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                Access.RefAccess(base, fieldAccessorFromAddr(expr))
            }

            // Index/element access
            is GoIRIndexExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                Access.RefAccess(base, ElementAccessor)
            }

            is GoIRIndexAddrExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                Access.RefAccess(base, ElementAccessor)
            }
            is GoIRLookupExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                Access.RefAccess(base, ElementAccessor)
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
                    Access.RefAccess(base, ElementAccessor)
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
                Access.RefAccess(base, tupleFieldAccessor(expr.extractIndex, expr.type))
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
        }
    }

    private fun singleOperandAccess(value: GoIRValue, method: GoIRFunction): Access? {
        val base = accessPathBase(value, method) { globalValue ->
            return Access.RefAccess(
                AccessPathBase.ClassStatic,
                ClassStaticAccessor(globalValue.global.fullName)
            )
        } ?: return null
        return Access.Simple(base)
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
            ?: return Access.Simple(AccessPathBase.LocalVar(addr.index))

        return when (val expr = (defInst as? GoIRAssignInst)?.expr) {
            is GoIRFieldAddrExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                Access.RefAccess(base, fieldAccessorFromAddr(expr))
            }
            is GoIRIndexAddrExpr -> {
                val base = accessPathBase(expr.x, method) ?: return null
                Access.RefAccess(base, ElementAccessor)
            }
            else -> Access.Simple(AccessPathBase.LocalVar(addr.index))
        }
    }

    // ── Field accessor helpers ───────────────────────────────────────

    fun tupleFieldAccessor(index: Int, elementType: GoIRType): FieldAccessor {
        return FieldAccessor("tuple", "\$$index", elementType.displayName)
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

    fun findDefInst(register: GoIRRegister, method: GoIRFunction): GoIRDefInst? {
        val body = method.body ?: return null
        return body.instructions.getOrNull(register.index) as? GoIRDefInst
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

    /**
     * Inspect an assignment's RHS for a "global read".
     *
     * Three SSA shapes lower to a tainted destination register:
     *
     *  1. `q := slice[i]` over a global-loaded slice, IR-as-IndexExpr:
     *       `GoIRIndexExpr(x = register-loaded-from-global)`
     *  2. `q := os.Args[1]` — the dominant CLI-input shape — which Go SSA splits
     *     into three steps:
     *       `t0 = *os.Args`            (GoIRUnOpExpr DEREF)
     *       `t1 = &t0[i]`              (GoIRIndexAddrExpr)
     *       `q  = *t1`                 (GoIRUnOpExpr DEREF)
     *     We fire on the outer DEREF, chasing one def-step through the
     *     `IndexAddrExpr` back to the global.
     *  3. `q := *globalVar` — a bare slice-as-a-whole load.
     *
     * Returns the global's `fullName` if one of the shapes matches.
     */
    fun detectGlobalReadName(inst: GoIRAssignInst, method: GoIRFunction): String? {
        val expr = inst.expr
        if (expr is GoIRIndexExpr) {
            return globalBehindValue(expr.x, method)
        }
        if (expr is GoIRUnOpExpr && expr.op == GoIRUnaryOp.DEREF) {
            val src = expr.x as? GoIRRegister
            if (src != null) {
                val srcDef = (findDefInst(src, method) as? GoIRAssignInst)?.expr
                if (srcDef is GoIRIndexAddrExpr) {
                    val behind = globalBehindValue(srcDef.x, method)
                    if (behind != null) return behind
                }
            }
        }
        val ops = expr.operands
        if (ops.size != 1) return null
        return (ops[0] as? GoIRGlobalValue)?.global?.fullName
    }

    private fun globalBehindValue(value: GoIRValue, method: GoIRFunction): String? {
        if (value is GoIRGlobalValue) return value.global.fullName
        if (value !is GoIRRegister) return null
        val defInst = findDefInst(value, method) as? GoIRAssignInst ?: return null
        val defOps = defInst.expr.operands
        if (defOps.size != 1) return null
        return (defOps[0] as? GoIRGlobalValue)?.global?.fullName
    }

    private val globalsNotSupportedReported = AtomicBoolean(false)
    private val logger = object : KLogging() {}.logger
}
