package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.jvm.ap.ifds.alias.Expr
import org.opentaint.dataflow.jvm.ap.ifds.alias.ExprOrValue
import org.opentaint.dataflow.jvm.ap.ifds.alias.InstEvalContext
import org.opentaint.dataflow.jvm.ap.ifds.alias.RefValue
import org.opentaint.dataflow.jvm.ap.ifds.alias.SimpleValue
import org.opentaint.dataflow.jvm.ap.ifds.alias.Stmt
import org.opentaint.dataflow.jvm.ap.ifds.alias.Value
import org.opentaint.dataflow.jvm.ap.ifds.alias.evalInst
import org.opentaint.ir.api.jvm.JIRField
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRCastExpr
import org.opentaint.ir.api.jvm.cfg.JIRCatchInst
import org.opentaint.ir.api.jvm.cfg.JIRClassConstant
import org.opentaint.ir.api.jvm.cfg.JIRConstant
import org.opentaint.ir.api.jvm.cfg.JIRExpr
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRNewArrayExpr
import org.opentaint.ir.api.jvm.cfg.JIRNewExpr
import org.opentaint.ir.api.jvm.cfg.JIRNullConstant
import org.opentaint.ir.api.jvm.cfg.JIRStringConstant

/**
 * The lowering of JIR statements to engine instructions (IMPL §4.1). It reads the `Stmt` of
 * `InstEvalContext.evalInst` (`JIRDSUAABuilder.kt`), as main does.
 *
 * - [evalCtx] makes the values of `this`, the arguments and the locals of the body.
 * - [bodyContext] is the context of the sites of the body.
 * - [contextOf] gives the engine context of a `RefValue.Local`.
 *
 * Calls: this step does not resolve calls. Each call is an [AliasInstr.UnresolvedCall] (a resolved
 * call is treated as unresolved until the step T6).
 */
internal class JIRAliasLowering(
    private val tables: AliasTables,
    private val evalCtx: InstEvalContext = RootEvalContext,
    private val bodyContext: Int = ROOT_CONTEXT,
    private val contextOf: (ContextInfo) -> Int = { ROOT_CONTEXT },
) {
    private val vars = tables.vars
    private val bases = tables.bases

    /** The engine instruction of [inst]. A statement without an alias effect gives [AliasInstr.Nop]. */
    fun lower(inst: JIRInst): AliasInstr {
        val stmt = evalCtx.evalInst(inst) ?: return AliasInstr.Nop
        return when (stmt) {
            is Stmt.Copy -> AliasInstr.Assign(local(stmt.lValue), ref(stmt.rValue))
            is Stmt.Assign -> lowerAssign(stmt, inst)
            is Stmt.FieldStore -> {
                val v = storedValue(stmt.value, inst) ?: return AliasInstr.Nop
                AliasInstr.FieldStore(ref(stmt.instance), cell(stmt.field), v)
            }

            is Stmt.ArrayStore -> {
                val v = storedValue(stmt.value, inst) ?: return AliasInstr.Nop
                AliasInstr.ArrayStore(ref(stmt.instance), v)
            }

            is Stmt.WriteStatic -> AliasInstr.StaticWrite
            is Stmt.Return -> AliasInstr.Return(stmt.value?.let(::ref) ?: stmt.constant?.let { constant(it, inst) })
            is Stmt.Throw -> AliasInstr.Throw(ref(stmt.value))
            is Stmt.Call -> {
                val args = ArrayList<AliasValue>(stmt.args.size + 1)
                stmt.instance?.let { v -> value(v, inst)?.let(args::add) }
                for (a in stmt.args) value(a, inst)?.let(args::add)
                AliasInstr.UnresolvedCall(site(inst), stmt.lValue?.let(::local), args)
            }
        }
    }

    /** The engine variable of a local of this body. */
    fun local(l: RefValue.Local): VarId = vars.local(l.idx, contextOf(l.ctx))

    private fun lowerAssign(stmt: Stmt.Assign, inst: JIRInst): AliasInstr {
        val dst = local(stmt.lValue)
        return when (val e = stmt.expr) {
            is Expr.FieldLoad -> when (val i = e.instance) {
                // The static key is the binary class name; the type name of RefValue.Static is recorded.
                is RefValue.Static -> AliasInstr.StaticRead(dst, bases.static(e.field.enclosingClass.name, i.type), cell(e.field))
                else -> AliasInstr.FieldLoad(dst, ref(i), cell(e.field))
            }

            is Expr.ArrayLoad -> AliasInstr.ArrayLoad(dst, ref(e.instance))
            else -> AliasInstr.Assign(dst, exprValue(e, inst))
        }
    }

    /** `value(v)` of a stored value. A primitive value is never stored: `null`. */
    private fun storedValue(v: ExprOrValue, inst: JIRInst): AliasValue? = when (v) {
        is SimpleValue.Primitive -> null
        is SimpleValue.RefConst -> constant(v, inst)
        is RefValue -> ref(v)
        is Expr -> exprValue(v, inst)
    }

    /** An argument or a receiver of a call. A primitive value gives `null`. */
    private fun value(v: Value, inst: JIRInst): AliasValue? = when (v) {
        is SimpleValue.Primitive -> null
        is SimpleValue.RefConst -> constant(v, inst)
        is RefValue -> ref(v)
    }

    /** The `Assign` rules of IMPL §4.1 for an expression that is not a load. */
    private fun exprValue(e: Expr, inst: JIRInst): AliasValue = when (e) {
        is Expr.Alloc -> alloc(e.stmt)
        is SimpleValue.RefConst -> constant(e, inst)
        // Unknown, a primitive, and a load in a stored value (not in three-address JIR): the unknown rule.
        else -> AliasValue.Fresh(site(inst))
    }

    private fun alloc(allocInst: JIRInst): AliasValue {
        val s = site(allocInst)
        if (allocInst !is JIRAssignInst) return AliasValue.Fresh(s) // catch (I2), other
        return when (val rhv = uncast(allocInst.rhv)) {
            is JIRNewExpr, is JIRNewArrayExpr -> AliasValue.New(s)
            is JIRCallExpr -> box(rhv, s)
            else -> AliasValue.Fresh(s)
        }
    }

    /** Box `valueOf` (I3): a constant argument gives `const(box type, constant)`; else `box(s)`. */
    private fun box(call: JIRCallExpr, s: SiteId): AliasValue {
        val arg = call.args.singleOrNull()
        if (arg !is JIRConstant) return AliasValue.Box(s)
        return AliasValue.Const(bases.const(call.method.method.enclosingClass.name, arg.toString()))
    }

    private fun constant(c: SimpleValue.RefConst, inst: JIRInst): AliasValue = when (val e = c.expr) {
        is JIRNullConstant -> AliasValue.Null(site(inst))
        is JIRStringConstant -> AliasValue.Const(bases.const(STRING_TYPE, e.value))
        is JIRClassConstant -> AliasValue.Const(bases.const(CLASS_TYPE, e.klass.typeName))
        else -> AliasValue.Const(bases.const(e.type.typeName, e.toString()))
    }

    private fun ref(v: RefValue): AliasValue.Ref = when (v) {
        is RefValue.Local -> AliasValue.Local(local(v))
        is RefValue.Arg -> AliasValue.Arg(v.idx)
        is RefValue.This -> AliasValue.This
        is RefValue.Static -> error("A static holder is not a value: $v")
    }

    private fun cell(field: JIRField): CellId =
        tables.cells.field(field.enclosingClass.name, field.name, field.type.typeName)

    private fun site(inst: JIRInst): SiteId = tables.sites.site(inst.location.index, bodyContext)

    private fun uncast(e: JIRExpr): JIRExpr = if (e is JIRCastExpr) uncast(e.operand) else e

    /** The values of the analyzed method: its own `this`, arguments and locals in the root context. */
    object RootEvalContext : InstEvalContext {
        override fun createThis(isOuter: Boolean): Value = RefValue.This(isOuter)
        override fun createArg(idx: Int): Value = RefValue.Arg(idx)
        override fun createLocal(idx: Int): RefValue.Local = RefValue.Local(idx, ContextInfo.rootContext)
    }
}
