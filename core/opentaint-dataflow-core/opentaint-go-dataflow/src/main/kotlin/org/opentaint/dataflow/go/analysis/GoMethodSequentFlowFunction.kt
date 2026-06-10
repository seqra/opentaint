package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access.RefAccess
import org.opentaint.dataflow.go.analysis.GoMethodCallResolver.ClosureCreationFlowFunction
import org.opentaint.dataflow.taint.TaintSourceActionEvaluator
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.expr.GoIRBinOpExpr
import org.opentaint.ir.go.expr.GoIRExpr
import org.opentaint.ir.go.expr.GoIRLookupExpr
import org.opentaint.ir.go.expr.GoIRMakeClosureExpr
import org.opentaint.ir.go.expr.GoIRNextExpr
import org.opentaint.ir.go.expr.GoIRTypeAssertExpr
import org.opentaint.ir.go.expr.GoIRUnOpExpr
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRFieldStore
import org.opentaint.ir.go.inst.GoIRGlobalStore
import org.opentaint.ir.go.inst.GoIRIndexStore
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.inst.GoIRMapUpdate
import org.opentaint.ir.go.inst.GoIRPhi
import org.opentaint.ir.go.inst.GoIRReturn
import org.opentaint.ir.go.inst.GoIRSend
import org.opentaint.ir.go.inst.GoIRStore
import org.opentaint.ir.go.inst.GoIRStoreInst
import org.opentaint.ir.go.type.GoIRBinaryOp

class GoMethodSequentFlowFunction(
    private val apManager: ApManager,
    private val context: GoMethodAnalysisContext,
    private val currentInst: GoIRInst,
    private val generateTrace: Boolean,
) : MethodSequentFlowFunction {

    private val method: GoIRFunction get() = context.method

    override fun propagateZeroToZero(): Set<Sequent> {
        val zeroSequents = mutableSetOf<Sequent>(Sequent.ZeroToZero)
        applyGlobalOrFieldReadSourceRules(zeroSequents)

        ClosureCreationFlowFunction.handle(currentInst) { base, accessors ->
            val startFact = apManager.createFinalAp(base, ExclusionSet.Universe)
            val fact = accessors.foldRight(startFact) { a, f -> f.prependAccessor(a) }
            zeroSequents += Sequent.ZeroToFact(fact, traceInfoOrNull())
        }

        return zeroSequents
    }

    private interface PropagationContext {
        fun unchanged()
        fun propagateFact(fact: FinalFactAp, trace: TraceInfo)
        fun propagateFactWithAccessorExclude(fact: FinalFactAp, accessor: Accessor, trace: TraceInfo)
        fun sideEffect(effect: Sequent.SideEffect)
    }

    override fun propagateZeroToFact(currentFactAp: FinalFactAp) =
        Z2FPropagationContext(currentFactAp).apply { propagate(currentFactAp) }.result

    override fun propagateFactToFact(initialFactAp: InitialFactAp, currentFactAp: FinalFactAp) =
        F2FPropagationContext(initialFactAp).apply { propagate(currentFactAp) }.result


    override fun propagateNDFactToFact(initialFacts: Set<InitialFactAp>, currentFactAp: FinalFactAp) =
        NDF2FPropagationContext(initialFacts, currentFactAp).apply { propagate(currentFactAp) }.result

    private fun PropagationContext.propagate(currentFact: FinalFactAp) {
        when (currentInst) {
            is GoIRAssignInst -> handleAssign(currentFact, currentInst)
            is GoIRStoreInst -> when (currentInst) {
                is GoIRStore -> handleStore(currentFact, currentInst)
                is GoIRFieldStore -> handleFieldStore(currentFact, currentInst)
                is GoIRIndexStore -> handleIndexStore(currentFact, currentInst)
            }

            is GoIRGlobalStore -> handleGlobalStore(currentFact, currentInst)
            is GoIRReturn -> handleReturn(currentFact, currentInst)
            is GoIRPhi -> handlePhi(currentFact, currentInst)
            is GoIRMapUpdate -> handleMapUpdate(currentFact, currentInst)
            is GoIRSend -> handleSend(currentFact, currentInst)
            else -> unchanged()
        }
    }

    private fun PropagationContext.handleAssign(
        currentFact: FinalFactAp,
        inst: GoIRAssignInst,
    ) {
        val registerBase = AccessPathBase.LocalVar(inst.register.index)
        if (currentFact.base != registerBase) {
            unchanged()
        }

        handleAssignedExpr(inst.expr, currentFact, registerBase, checkCommaOk = true)
    }

    private fun PropagationContext.handleAssignedExpr(
        expr: GoIRExpr,
        currentFact: FinalFactAp,
        registerBase: AccessPathBase.LocalVar,
        checkCommaOk: Boolean,
    ) {
        if (checkCommaOk) {
            val commaOk = when (expr) {
                is GoIRLookupExpr -> expr.commaOk
                is GoIRTypeAssertExpr -> expr.commaOk
                is GoIRUnOpExpr -> expr.commaOk
                else -> false
            }

            if (commaOk) {
                CommaOkPropagationContext(registerBase, this)
                    .handleAssignedExpr(expr, currentFact, registerBase, checkCommaOk = false)
                return
            }
        }

        if (expr is GoIRBinOpExpr && expr.op == GoIRBinaryOp.ADD
            && GoFlowFunctionUtils.isStringType(expr.type)
        ) {
            return handleStringConcat(currentFact, registerBase, expr)
        }

        if (expr is GoIRMakeClosureExpr) {
            return handleMakeClosure(currentFact, registerBase, expr)
        }

        if (expr is GoIRNextExpr) {
            return handleNext(currentFact, registerBase, expr)
        }

        val rhsAccess = GoFlowFunctionUtils.exprToAccess(expr, method)
            ?: return

        return when (rhsAccess) {
            is Access.Simple -> handleSimpleAssign(currentFact, registerBase, rhsAccess.base)
            is RefAccess -> handleNormalRefAssign(currentFact, registerBase, rhsAccess)
        }
    }

    private fun PropagationContext.handleSimpleAssign(
        currentFact: FinalFactAp,
        toBase: AccessPathBase,
        fromBase: AccessPathBase,
        additionFactsOnAssign: (FinalFactAp) -> List<FinalFactAp> = { emptyList() }
    ) {
        if (currentFact.base != toBase) {
            unchanged()
        }

        if (fromBase == toBase) {
            unchanged()
            return
        }

        // Gen: if fact is about the source, generate taint on destination
        if (currentFact.base == fromBase) {
            val newFact = currentFact.rebase(toBase)
            propagateFact(newFact, TraceInfo.Flow)

            additionFactsOnAssign(newFact).forEach {
                propagateFact(it, TraceInfo.Flow)
            }
        }
    }

    private fun PropagationContext.handleMakeClosure(
        currentFact: FinalFactAp,
        registerBase: AccessPathBase,
        expr: GoIRMakeClosureExpr,
    ) {
        for ((i, binding) in expr.bindings.withIndex()) {
            val bindingBase = GoFlowFunctionUtils.accessPathBase(binding, method)
            if (currentFact.base == bindingBase) {
                val freeVarFact = currentFact.rebase(registerBase)
                    .prependAccessor(GoFlowFunctionUtils.freeVarAccessor(expr.fn, i))
                propagateFact(freeVarFact, TraceInfo.Flow)
            }
        }
    }

    private fun PropagationContext.handleStringConcat(
        currentFact: FinalFactAp,
        registerBase: AccessPathBase,
        expr: GoIRBinOpExpr,
    ) {
        val leftBase = GoFlowFunctionUtils.accessPathBase(expr.x, method)
        val rightBase = GoFlowFunctionUtils.accessPathBase(expr.y, method)

        if (currentFact.base == leftBase || currentFact.base == rightBase) {
            propagateFact(currentFact.rebase(registerBase), TraceInfo.Flow)
        }
    }

    private fun PropagationContext.handleNext(
        currentFact: FinalFactAp,
        registerBase: AccessPathBase,
        expr: GoIRNextExpr,
    ) {
        val iterBase = GoFlowFunctionUtils.accessPathBase(expr.iter, method)

        return handleComplexRefAssign(
            currentFact, registerBase,
            RefAccess(iterBase, ElementAccessor)
        ) { elementFact ->
            GoFlowFunctionUtils.rangeElementTupleSlots(expr, method).map { slot ->
                elementFact.rebase(registerBase).prependAccessor(slot)
            }
        }
    }

    private fun PropagationContext.handleNormalRefAssign(
        currentFact: FinalFactAp,
        toBase: AccessPathBase,
        rhsAccess: RefAccess,
    ) = handleComplexRefAssign(currentFact, toBase, rhsAccess) { fact ->
        listOf(fact.rebase(toBase))
    }

    private fun PropagationContext.handleComplexRefAssign(
        currentFact: FinalFactAp,
        toBase: AccessPathBase,
        rhsAccess: RefAccess,
        mkAssignedFacts: (FinalFactAp) -> List<FinalFactAp>,
    ) {
        if (currentFact.base != rhsAccess.base) return

        if (currentFact.isAbstract() && !currentFact.exclusions.contains(rhsAccess.accessor)) {
            propagateFactWithAccessorExclude(currentFact, rhsAccess.accessor, TraceInfo.Flow)

            val nonAbstractFact = currentFact.removeAbstraction()
            if (nonAbstractFact != null) {
                handleComplexRefAssign(nonAbstractFact, toBase, rhsAccess, mkAssignedFacts)
            }
            return
        }

        if (!currentFact.startsWithAccessor(rhsAccess.accessor)) return

        val readFact = currentFact.readAccessor(rhsAccess.accessor)
        if (readFact != null) {
            mkAssignedFacts(readFact).forEach {
                propagateFact(it, TraceInfo.Flow)
            }
        }
    }

    private fun PropagationContext.handleStore(
        currentFact: FinalFactAp,
        inst: GoIRStore,
    ) {
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
        val dstBase = GoFlowFunctionUtils.accessPathBase(inst.addr, method)

        return handleSimpleAssign(currentFact, dstBase, valueBase) { fact ->
            val aliased = mutableListOf<FinalFactAp>()
            context.aliasAnalysis.forEachAliasAtStatement(currentInst, fact) {
                aliased += it
            }
            aliased
        }
    }

    private fun PropagationContext.handleFieldStore(
        currentFact: FinalFactAp,
        inst: GoIRFieldStore,
    ) {
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
        val instance = GoFlowFunctionUtils.accessPathBase(inst.base, method)

        val access = RefAccess(instance, GoFlowFunctionUtils.fieldAccessorFromStore(inst))
        return complexAccessorWrite(access, currentFact, valueBase)
    }

    private fun PropagationContext.handleIndexStore(
        currentFact: FinalFactAp,
        inst: GoIRIndexStore,
    ) {
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
        val instance = GoFlowFunctionUtils.accessPathBase(inst.base, method)

        val access = RefAccess(instance, ElementAccessor)
        return complexAccessorWrite(access, currentFact, valueBase)
    }

    private fun PropagationContext.complexAccessorWrite(
        writeTo: RefAccess,
        currentFact: FinalFactAp,
        valueBase: AccessPathBase
    ) {
        val destBase = writeTo.base
        val accessor = writeTo.accessor

        if (currentFact.base == valueBase) {
            unchanged()

            val newFact = currentFact.rebase(destBase).prependAccessor(accessor)
            propagateFact(newFact, TraceInfo.Flow)

            context.aliasAnalysis.forEachAliasAtStatement(currentInst, newFact) { aliased ->
                propagateFact(aliased, TraceInfo.Flow)
            }

            check(destBase != valueBase) { "todo: write to same location" }
            return
        }

        if (currentFact.base != destBase) {
            unchanged()
            return
        }

        if (accessor is ElementAccessor) {
            // Weak update for elements
            propagateFact(currentFact, TraceInfo.Flow)
            return
        }

        if (currentFact.isAbstract() && !currentFact.exclusions.contains(accessor)) {
            propagateFactWithAccessorExclude(currentFact, accessor, TraceInfo.Flow)

            val nonAbstractFact = currentFact.removeAbstraction()
            if (nonAbstractFact != null) {
                complexAccessorWrite(writeTo, nonAbstractFact, valueBase)
            }
            return
        }

        if (!currentFact.startsWithAccessor(accessor)) {
            propagateFact(currentFact, TraceInfo.Flow)
            return
        }

        val cleaned = currentFact.clearAccessor(accessor)
        if (cleaned != null) {
            propagateFact(cleaned, TraceInfo.Flow)
        }
    }

    private fun PropagationContext.handleGlobalStore(
        currentFact: FinalFactAp,
        inst: GoIRGlobalStore,
    ) {
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
        val globalAccess = GoFlowFunctionUtils.accessForGlobal(inst.global)

        return complexAccessorWrite(globalAccess, currentFact, valueBase)
    }

    private fun PropagationContext.handleReturn(
        currentFact: FinalFactAp,
        inst: GoIRReturn,
    ) {
        unchanged()

        for ((i, retVal) in inst.results.withIndex()) {
            val retBase = GoFlowFunctionUtils.accessPathBase(retVal, method)
            if (currentFact.base == retBase) {
                val exitFact = if (inst.results.size == 1) {
                    currentFact.rebase(AccessPathBase.Return)
                } else {
                    val tupleAccessor = GoFlowFunctionUtils.tupleFieldAccessor(i)
                    currentFact.rebase(AccessPathBase.Return).prependAccessor(tupleAccessor)
                }

                propagateFact(exitFact, TraceInfo.Flow)
            }
        }
    }

    private fun PropagationContext.handlePhi(
        currentFact: FinalFactAp,
        inst: GoIRPhi,
    ) {
        val registerBase = AccessPathBase.LocalVar(inst.register.index)
        if (currentFact.base != registerBase) {
            unchanged()
        }

        for (edge in inst.edges.values) {
            val edgeBase = GoFlowFunctionUtils.accessPathBase(edge, method)
            if (currentFact.base == edgeBase) {
                val newFact = currentFact.rebase(registerBase)
                propagateFact(newFact, TraceInfo.Flow)
            }
        }
    }

    private fun PropagationContext.handleMapUpdate(
        currentFact: FinalFactAp,
        inst: GoIRMapUpdate,
    ) {
        val mapBase = GoFlowFunctionUtils.accessPathBase(inst.map, method)
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
        val keyBase = GoFlowFunctionUtils.accessPathBase(inst.key, method)

        val mapAccess = RefAccess(mapBase, ElementAccessor)
        complexAccessorWrite(mapAccess, currentFact, valueBase)
        complexAccessorWrite(mapAccess, currentFact, keyBase)
    }

    private fun PropagationContext.handleSend(
        currentFact: FinalFactAp,
        inst: GoIRSend,
    ) {
        val chanBase = GoFlowFunctionUtils.accessPathBase(inst.chan, method)
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.x, method)

        val chanAccess = RefAccess(chanBase, ElementAccessor)
        complexAccessorWrite(chanAccess, currentFact, valueBase)
    }

    private fun applyGlobalOrFieldReadSourceRules(out: MutableSet<Sequent>) {
        applyGlobalOrFieldReadSourceRules(
            currentInst, context,
            mkSourceEvaluator = { TaintSourceActionEvaluator(apManager, ExclusionSet.Universe) }
        ) { rule, action, lhv, fact ->
            val trace = TraceInfo.Rule(rule, action)
            if (fact.base !is AccessPathBase.Return) {
                TODO("Field/global source with non-result assign")
            }
            out += Sequent.ZeroToFact(fact.rebase(lhv), trace)
        }
    }

    private fun traceInfoOrNull(): TraceInfo? = if (generateTrace) TraceInfo.Flow else null

    private abstract class DefaultPropagationContext : PropagationContext {
        val result = hashSetOf<Sequent>()

        override fun unchanged() {
            result.add(Sequent.Unchanged)
        }

        override fun sideEffect(effect: Sequent.SideEffect) {
            result.add(effect)
        }
    }

    private class Z2FPropagationContext(private val currentFactAp: FinalFactAp) : DefaultPropagationContext() {
        override fun propagateFact(fact: FinalFactAp, trace: TraceInfo) {
            result.add(Sequent.ZeroToFact(fact, trace))
        }

        override fun propagateFactWithAccessorExclude(fact: FinalFactAp, accessor: Accessor, trace: TraceInfo) {
            error("Zero to Fact edge can't be refined: $currentFactAp")
        }
    }

    private class F2FPropagationContext(
        private val initialFactAp: InitialFactAp
    ) : DefaultPropagationContext() {
        override fun propagateFact(fact: FinalFactAp, trace: TraceInfo) {
            result.add(Sequent.FactToFact(initialFactAp, fact, trace))
        }

        override fun propagateFactWithAccessorExclude(fact: FinalFactAp, accessor: Accessor, trace: TraceInfo) {
            val refinedInitial = initialFactAp.exclude(accessor)
            val refinedFact = fact.exclude(accessor)
            result.add(Sequent.FactToFact(refinedInitial, refinedFact, trace))

            result.add(Sequent.SideEffectRequirement(refinedInitial))
        }
    }

    private class NDF2FPropagationContext(
        private val initialFacts: Set<InitialFactAp>,
        private val currentFactAp: FinalFactAp
    ) : DefaultPropagationContext() {
        override fun propagateFact(fact: FinalFactAp, trace: TraceInfo) {
            result.add(Sequent.NDFactToFact(initialFacts, fact, trace))
        }

        override fun propagateFactWithAccessorExclude(fact: FinalFactAp, accessor: Accessor, trace: TraceInfo) {
            error("NDF2F edge can't be refined: $currentFactAp")
        }
    }

    private class CommaOkPropagationContext(
        val resultRegister: AccessPathBase,
        val base: PropagationContext
    ) : PropagationContext by base {
        private val valueSlot = GoFlowFunctionUtils.tupleFieldAccessor(0)

        private fun FinalFactAp.applyCommaOk(): FinalFactAp {
            if (base != resultRegister) return this
            return prependAccessor(valueSlot)
        }

        override fun propagateFact(fact: FinalFactAp, trace: TraceInfo) {
            base.propagateFact(fact.applyCommaOk(), trace)
        }

        override fun propagateFactWithAccessorExclude(fact: FinalFactAp, accessor: Accessor, trace: TraceInfo) {
            base.propagateFactWithAccessorExclude(fact.applyCommaOk(), accessor, trace)
        }
    }
}
