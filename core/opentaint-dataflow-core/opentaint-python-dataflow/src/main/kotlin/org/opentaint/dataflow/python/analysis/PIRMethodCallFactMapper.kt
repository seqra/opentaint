package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.ReadableAccessorList
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.SELF_ACCESSOR
import org.opentaint.dataflow.python.adapter.PIRCallExprAdapter
import org.opentaint.dataflow.python.pIRDowncast
import org.opentaint.dataflow.python.util.PIRFlowFunctionUtils
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.api.python.*

/**
 * Maps facts between caller and callee frames at call boundaries.
 *
 * Offset-blind: the core mapping methods align `call.args[i]` with
 * callee `Argument(i)` positionally with no shift for `self`/`cls`.
 * All implicit-parameter offset arithmetic is encapsulated in
 * [offsetEnter] / [offsetExit], which are invoked only by
 * [PIRMethodCallResolver] and [PIRMethodCallSummaryHandler].
 */
object PIRMethodCallFactMapper : MethodCallFactMapper {

    private fun valueToBase(value: PIRValue): AccessPathBase? =
        PIRFlowFunctionUtils.accessPathBase(value)

    override fun mapMethodExitToReturnFlowFact(
        callStatement: CommonInst,
        factAp: FinalFactAp,
        checker: FactTypeChecker,
    ): List<FinalFactAp> {
        pIRDowncast<PIRCall>(callStatement)
        return listOfNotNull(
            mapMethodExitToReturnFlowFact(callStatement, factAp, FinalFactAp::rebase, FinalFactAp::prependAccessor)
        )
    }

    override fun mapMethodExitToReturnFlowFact(
        callStatement: CommonInst,
        factAp: InitialFactAp,
    ): List<InitialFactAp> {
        pIRDowncast<PIRCall>(callStatement)
        return listOfNotNull(
            mapMethodExitToReturnFlowFact(callStatement, factAp, InitialFactAp::rebase, InitialFactAp::prependAccessor)
        )
    }

    override fun mapMethodCallToStartFlowFact(
        callStatement: CommonInst,
        callee: CommonMethod,
        callExpr: CommonCallExpr,
        returnValue: CommonValue?,
        factAp: FinalFactAp,
        checker: FactTypeChecker,
        onMappedFact: (FinalFactAp, AccessPathBase) -> Unit,
    ) {
        pIRDowncast<PIRCall>(callStatement)
        mapMethodCallToStartFlowFact(callStatement, factAp, onMappedFact)
    }

    override fun mapMethodCallToStartFlowFact(
        callStatement: CommonInst,
        callee: CommonMethod,
        callExpr: CommonCallExpr,
        returnValue: CommonValue?,
        fact: InitialFactAp,
        onMappedFact: (InitialFactAp, AccessPathBase) -> Unit,
    ) {
        pIRDowncast<PIRCall>(callStatement)
        mapMethodCallToStartFlowFact(callStatement, fact, onMappedFact)
    }

    fun mapLoadAttributeFactToStart(
        statement: PIRLoadAttr,
        fact: FinalFactAp,
        onMappedFact: (FinalFactAp, AccessPathBase) -> Unit,
    ) {
        val objBase = valueToBase(statement.obj) ?: return

        if (objBase == fact.base) {
            onMappedFact(fact, AccessPathBase.This)
        }
    }

    fun mapLoadAttributeFactToReturn(statement: PIRLoadAttr, fact: FinalFactAp): FinalFactAp? =
        when (fact.base) {
            is AccessPathBase.Return -> valueToBase(statement.target)?.let { fact.rebase(it) }
            is AccessPathBase.This -> valueToBase(statement.obj)?.let { fact.rebase(it) }
            else -> null
        }

    private fun <F : FactAp> mapMethodExitToReturnFlowFact(
        call: PIRCall,
        factAp: F,
        rebase: F.(AccessPathBase) -> F,
        prepend: F.(Accessor) -> F,
    ): F? {
        return when (val base = factAp.base) {
            is AccessPathBase.Argument -> {
                val argValue = call.args.getOrNull(base.idx)?.value ?: return null
                val callerBase = valueToBase(argValue) ?: return null
                factAp.rebase(callerBase)
            }
            is AccessPathBase.Return -> {
                val target = call.target ?: return null
                val targetBase = valueToBase(target) ?: return null
                factAp.rebase(targetBase)
            }
            is AccessPathBase.This -> {
                // Inverse of the enter strip: re-prepend $PIR_SELF onto the callee temp
                // ($t0), encoding "the receiver of $t0". Intra-procedural alias analysis
                // resolves $t0.$PIR_SELF back to the concrete receiver.
                val calleeBase = valueToBase(call.callee) ?: return null
                factAp.prepend(SELF_ACCESSOR).rebase(calleeBase)
            }
            is AccessPathBase.LocalVar -> null // Cannot escape
            is AccessPathBase.ClassStatic -> factAp
            is AccessPathBase.Constant -> factAp
            else -> null
        }
    }

    private fun <F> mapMethodCallToStartFlowFact(
        call: PIRCall,
        factAp: F,
        onMappedFact: (F, AccessPathBase) -> Unit,
    ) where F : FactAp, F : ReadableAccessorList<F> {
        val base = factAp.base

        for ((i, arg) in call.args.withIndex()) {
            val argBase = valueToBase(arg.value) ?: continue
            if (base == argBase) {
                val startBase = AccessPathBase.Argument(i)
                onMappedFact(factAp, startBase)
            }
        }

        if (valueToBase(call.callee) == base) {
            val selfFact = factAp.readAccessor(SELF_ACCESSOR)
            selfFact?.let { onMappedFact(it, AccessPathBase.This) }
        }

        if (base is AccessPathBase.ClassStatic) {
            onMappedFact(factAp, base)
        }
    }

    override fun factIsRelevantToMethodCall(
        callStatement: CommonInst,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        factAp: FactAp,
    ): Boolean {
        pIRDowncast<PIRCall>(callStatement)
        pIRDowncast<PIRLocalVar?>(returnValue)
        pIRDowncast<PIRCallExprAdapter>(callExpr)

        return factIsRelevantToMethodCall(callStatement, returnValue, callExpr, factAp)
    }

    private fun factIsRelevantToMethodCall(
        callStatement: PIRCall,
        returnValue: PIRValue?,
        callExpr: PIRCallExprAdapter,
        factAp: FactAp,
    ): Boolean {
        val base = factAp.base
        if (base is AccessPathBase.ClassStatic || base is AccessPathBase.Constant) return true
        if (valueToBase(callStatement.callee) == base) return true

        for (arg in callStatement.args) {
            if (base == valueToBase(arg.value)) return true
        }

        if (returnValue != null) {
            if (base == valueToBase(returnValue)) return true
        }

        return false
    }

    override fun isValidMethodExitFact(factAp: FactAp): Boolean =
        factAp.base !is AccessPathBase.LocalVar

    /**
     * Translates an offset-free [base] into the callee's frame when
     * entering [callee] at [callSite]. For implicit-parameter callees
     * (instance methods, classmethods), maps `Argument(i)` to
     * `Argument(i + offset)` and the receiver marker `This` to the
     * implicit first parameter `Argument(0)`. Other bases are returned
     * unchanged.
     *
     * Returns null when the shifted Argument would exceed the callee's
     * formal parameter count (avoids AccessPathBaseStorage crashes on
     * extra positional args), or when a `This` receiver reaches a callee
     * with no implicit parameter (static/module function).
     *
     * Only invoked from [PIRMethodCallResolver].
     */
    fun offsetEnter(callSite: PIRCall, callee: PIRFunction, base: AccessPathBase): AccessPathBase? {
        val offset = PIRFlowFunctionUtils.implicitParamOffset(callee)
        return when (base) {
            // Offset-free receiver marker → the implicit first parameter (self/cls).
            // Dropped for callees with no implicit parameter (static/module functions).
            is AccessPathBase.This -> if (offset > 0) AccessPathBase.Argument(0) else null
            is AccessPathBase.Argument -> {
                val newIdx = base.idx + offset
                if (newIdx >= callee.parameters.size) null else AccessPathBase.Argument(newIdx)
            }
            else -> base
        }
    }

    /**
     * Inverse of [offsetEnter]: translates a callee-frame [base] back to
     * the offset-free frame when returning from [callee] at [callSite].
     * Maps the implicit first parameter `Argument(0)` to the receiver
     * marker `This`, and other `Argument(i)` to `Argument(i - offset)`.
     * Returns null when the shifted Argument would underflow.
     *
     * Only invoked from [PIRMethodCallSummaryHandler].
     */
    fun offsetExit(callSite: PIRCall, callee: PIRFunction, base: AccessPathBase): AccessPathBase? {
        if (base !is AccessPathBase.Argument) return base
        val offset = PIRFlowFunctionUtils.implicitParamOffset(callee)
        // The implicit first parameter (self/cls) maps back to the offset-free receiver marker.
        if (offset > 0 && base.idx == 0) return AccessPathBase.This
        val newIdx = base.idx - offset
        if (newIdx < 0) return null
        return AccessPathBase.Argument(newIdx)
    }
}
