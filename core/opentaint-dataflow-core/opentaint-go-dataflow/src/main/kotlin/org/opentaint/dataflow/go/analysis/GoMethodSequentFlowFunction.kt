package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.configuration.isTrue
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access
import org.opentaint.dataflow.go.GoFlowFunctionUtils.resolvePosAccess
import org.opentaint.dataflow.go.analysis.GoMethodCallResolver.ClosureCreationFlowFunction
import org.opentaint.dataflow.go.rules.TaintRule
import org.opentaint.dataflow.taint.TaintSourceActionEvaluator
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.expr.GoIRBinOpExpr
import org.opentaint.ir.go.expr.GoIRMakeClosureExpr
import org.opentaint.ir.go.expr.GoIRNextExpr
import org.opentaint.ir.go.expr.GoIRTypeAssertExpr
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRGlobalStore
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.inst.GoIRMapUpdate
import org.opentaint.ir.go.inst.GoIRPhi
import org.opentaint.ir.go.inst.GoIRReturn
import org.opentaint.ir.go.inst.GoIRSend
import org.opentaint.ir.go.inst.GoIRStore
import org.opentaint.ir.go.type.GoIRBinaryOp
import org.opentaint.util.onSome

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

    override fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<Sequent> {
        return propagate(null, currentFactAp)
    }

    override fun propagateFactToFact(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
    ): Set<Sequent> {
        return propagate(initialFactAp, currentFactAp)
    }

    override fun propagateNDFactToFact(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
    ): Set<Sequent> {
        return setOf(Sequent.Unchanged)
    }

    private fun propagate(initialFact: InitialFactAp?, currentFact: FinalFactAp): Set<Sequent> {
        return when (currentInst) {
            is GoIRAssignInst -> handleAssign(initialFact, currentFact, currentInst)
            is GoIRStore -> handleStore(initialFact, currentFact, currentInst)
            is GoIRGlobalStore -> handleGlobalStore(initialFact, currentFact, currentInst)
            is GoIRReturn -> handleReturn(initialFact, currentFact, currentInst)
            is GoIRPhi -> handlePhi(initialFact, currentFact, currentInst)
            is GoIRMapUpdate -> handleMapUpdate(initialFact, currentFact, currentInst)
            is GoIRSend -> handleSend(initialFact, currentFact, currentInst)
            else              -> setOf(Sequent.Unchanged)
        }
    }

    private fun handleAssign(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        inst: GoIRAssignInst,
    ): Set<Sequent> {
        val registerBase = AccessPathBase.LocalVar(inst.register.index)
        val expr = inst.expr

        if (expr is GoIRBinOpExpr && expr.op == GoIRBinaryOp.ADD
            && GoFlowFunctionUtils.isStringType(expr.type)
        ) {
            return handleStringConcat(initialFact, currentFact, registerBase, expr)
        }

        if (expr is GoIRTypeAssertExpr && expr.commaOk) {
            return handleCommaOkTypeAssert(initialFact, currentFact, registerBase, expr)
        }

        if (expr is GoIRMakeClosureExpr) {
            return handleMakeClosure(initialFact, currentFact, registerBase, expr)
        }
        val rhsAccess = GoFlowFunctionUtils.exprToAccess(expr, method)
            ?: return handleNonPropagatingExpr(currentFact, registerBase)

        return when (rhsAccess) {
            is Access.Simple -> handleSimpleAssign(initialFact, currentFact, registerBase, rhsAccess.base)
            is Access.RefAccess -> handleRefAssign(initialFact, currentFact, registerBase, rhsAccess)
        }
    }

    private fun handleSimpleAssign(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        toBase: AccessPathBase,
        fromBase: AccessPathBase,
    ): Set<Sequent> {
        val result = mutableSetOf<Sequent>()

        // Kill: if fact is about the destination, the assignment overwrites it
        if (currentFact.base == toBase) {
            if (fromBase == toBase) {
                result.add(Sequent.Unchanged)
                return result
            }
            // Don't add Unchanged — fact is killed
        } else {
            result.add(Sequent.Unchanged)
        }

        // Gen: if fact is about the source, generate taint on destination
        if (currentFact.base == fromBase) {
            val newFact = currentFact.rebase(toBase)
            result.add(makeEdge(initialFact, newFact))
        }

        return result
    }

    private fun handleMakeClosure(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        registerBase: AccessPathBase,
        expr: GoIRMakeClosureExpr,
    ): Set<Sequent> {
        val result = mutableSetOf<Sequent>()

        if (currentFact.base != registerBase) {
            result.add(Sequent.Unchanged)
        }

        for ((i, binding) in expr.bindings.withIndex()) {
            val bindingBase = GoFlowFunctionUtils.accessPathBase(binding, method) ?: continue
            if (currentFact.base == bindingBase) {
                val freeVarFact = currentFact.rebase(registerBase)
                    .prependAccessor(GoFlowFunctionUtils.freeVarAccessor(expr.fn, i))
                result.add(makeEdge(initialFact, freeVarFact))
            }
        }

        return result
    }

    // Backward counterpart: GoMethodSequentPrecondition.handleCommaOkTypeAssertPrecondition — keep in lockstep (same tuple$0 slot, same commaOk guard).
    private fun handleCommaOkTypeAssert(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        registerBase: AccessPathBase,
        expr: GoIRTypeAssertExpr,
    ): Set<Sequent> {
        val result = mutableSetOf<Sequent>()

        // Kill: the register is overwritten by the assert result.
        if (currentFact.base != registerBase) {
            result.add(Sequent.Unchanged)
        }

        // Gen: if the operand carries a fact, taint the value slot (tuple index 0)
        // of the (value, ok) result. The `ok` bool slot stays clean.
        val operandBase = GoFlowFunctionUtils.accessPathBase(expr.x, method)
        if (operandBase != null && currentFact.base == operandBase) {
            val valueSlot = GoFlowFunctionUtils.tupleFieldAccessor(0, expr.assertedType)
            val newFact = currentFact.rebase(registerBase).prependAccessor(valueSlot)
            result.add(makeEdge(initialFact, newFact))
        }

        return result
    }

    private fun handleNext(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        registerBase: AccessPathBase,
        expr: GoIRNextExpr,
    ): Set<Sequent> {
        val iterBase = GoFlowFunctionUtils.accessPathBase(expr.iter, method)
            ?: return handleNonPropagatingExpr(currentFact, registerBase)

        val result = handleSimpleAssign(initialFact, currentFact, registerBase, iterBase).toMutableSet()

        if (currentFact.base == iterBase && currentFact.startsWithAccessor(ElementAccessor)) {
            val element = currentFact.readAccessor(ElementAccessor)
            if (element != null) {
                for (slot in GoFlowFunctionUtils.rangeElementTupleSlots(expr, method)) {
                    val slotFact = element.rebase(registerBase).prependAccessor(slot)
                    result.add(makeEdge(initialFact, slotFact))
                }
            }
        }

        return result
    }

    private fun handleRefAssign(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        toBase: AccessPathBase,
        rhsAccess: Access.RefAccess,
    ): Set<Sequent> {
        val result = mutableSetOf<Sequent>()

        // Kill: assignment to register overwrites previous value
        if (currentFact.base == toBase) {
            // Don't add Unchanged — register gets new value
        } else {
            result.add(Sequent.Unchanged)
        }

        // Gen: if fact is about the source object AND the accessor matches
        if (currentFact.base == rhsAccess.base) {
            if (currentFact.startsWithAccessor(rhsAccess.accessor)) {
                // Concrete: strip accessor and rebase
                val readFact = currentFact.readAccessor(rhsAccess.accessor)
                if (readFact != null) {
                    result.add(makeEdge(initialFact, readFact.rebase(toBase)))
                }
            } else if (currentFact.isAbstract()
                && !currentFact.exclusions.contains(rhsAccess.accessor)
            ) {
                // Abstract: trigger refinement by adding accessor to exclusion set
                val refinedFact = currentFact.exclude(rhsAccess.accessor)
                result.add(makeEdge(initialFact, refinedFact))
            }
        }

        return result
    }

    private fun handleStore(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        inst: GoIRStore,
    ): Set<Sequent> {
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
            ?: return setOf(Sequent.Unchanged)
        val addrAccess = GoFlowFunctionUtils.accessForAddr(inst.addr, method)
            ?: return setOf(Sequent.Unchanged)

        return complexAccessorWrite(addrAccess, currentFact, initialFact, valueBase) { _, _ ->
            val chain = GoFlowFunctionUtils.resolveAddrChain(inst.addr, method)
                ?: return@complexAccessorWrite emptyList()

            listOf(chain)
        }
    }

    private fun complexAccessorWrite(
        writeTo: Access,
        currentFact: FinalFactAp,
        initialFact: InitialFactAp?,
        valueBase: AccessPathBase,
        writeToMemoryAliases: (AccessPathBase, Accessor) -> List<Pair<AccessPathBase, List<Accessor>>>
    ): MutableSet<Sequent> {
        val result = mutableSetOf<Sequent>()

        when (writeTo) {
            is Access.RefAccess -> {
                val destBase = writeTo.base
                val accessor = writeTo.accessor

                // Kill/preserve
                if (currentFact.base == destBase) {
                    if (currentFact.startsWithAccessor(accessor)) {
                        if (accessor is ElementAccessor) {
                            result.add(Sequent.Unchanged) // Weak update for elements
                        }
                        // FieldAccessor: strong update — don't preserve
                    } else if (currentFact.isAbstract()
                        && !currentFact.exclusions.contains(accessor)
                    ) {
                        val refinedFact = currentFact.exclude(accessor)
                        result.add(makeEdge(initialFact, refinedFact))
                    } else {
                        result.add(Sequent.Unchanged)
                    }
                } else {
                    result.add(Sequent.Unchanged)
                }

                if (currentFact.base == valueBase) {
                    val newFact = currentFact.rebase(destBase).prependAccessor(accessor)
                    result.add(makeEdge(initialFact, newFact))

                    writeToMemoryAliases(destBase, accessor).forEach { (rootBase, accessors) ->
                        val newAliasedFact = accessors.fold(currentFact.rebase(rootBase)) { f, acc ->
                            f.prependAccessor(acc)
                        }
                        result.add(makeEdge(initialFact, newAliasedFact))
                    }
                }
            }

            is Access.Simple -> {
                val destBase = writeTo.base

                if (currentFact.base == destBase) {
                    // Pointer store: overwritten
                } else {
                    result.add(Sequent.Unchanged)
                }

                if (currentFact.base == valueBase) {
                    val newFact = currentFact.rebase(destBase)
                    result.add(makeEdge(initialFact, newFact))
                }
            }
        }

        return result
    }

    private fun handleGlobalStore(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        inst: GoIRGlobalStore,
    ): Set<Sequent> {
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
            ?: return setOf(Sequent.Unchanged)

        val globalAccess = GoFlowFunctionUtils.accessForGlobal(inst.global)

        return complexAccessorWrite(globalAccess, currentFact, initialFact, valueBase) { _, _ -> emptyList() }
    }

    private fun handleReturn(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        inst: GoIRReturn,
    ): Set<Sequent> {
        val result = mutableSetOf<Sequent>(Sequent.Unchanged)

        if (inst.results.size == 1) {
            val retBase = GoFlowFunctionUtils.accessPathBase(inst.results[0], method) ?: return result
            if (currentFact.base == retBase) {
                val exitFact = currentFact.rebase(AccessPathBase.Return)
                result.add(makeEdge(initialFact, exitFact))
            }
        } else {
            for ((i, retVal) in inst.results.withIndex()) {
                val retBase = GoFlowFunctionUtils.accessPathBase(retVal, method) ?: continue
                if (currentFact.base == retBase) {
                    val tupleAccessor = GoFlowFunctionUtils.tupleFieldAccessor(i, retVal.type)
                    val exitFact = currentFact.rebase(AccessPathBase.Return).prependAccessor(tupleAccessor)
                    result.add(makeEdge(initialFact, exitFact))
                }
            }
        }

        return result
    }

    private fun handlePhi(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        inst: GoIRPhi,
    ): Set<Sequent> {
        val result = mutableSetOf<Sequent>()
        val registerBase = AccessPathBase.LocalVar(inst.register.index)

        if (currentFact.base == registerBase) {
            // Don't add Unchanged — overwritten by phi
        } else {
            result.add(Sequent.Unchanged)
        }

        for (edge in inst.edges.values) {
            val edgeBase = GoFlowFunctionUtils.accessPathBase(edge, method) ?: continue
            if (currentFact.base == edgeBase) {
                val newFact = currentFact.rebase(registerBase)
                result.add(makeEdge(initialFact, newFact))
                break
            }
        }

        return result
    }

    private fun handleMapUpdate(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        inst: GoIRMapUpdate,
    ): Set<Sequent> {
        val result = mutableSetOf<Sequent>(Sequent.Unchanged)
        val mapBase = GoFlowFunctionUtils.accessPathBase(inst.map, method)
            ?: return setOf(Sequent.Unchanged)
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
            ?: return setOf(Sequent.Unchanged)
        val keyBase = GoFlowFunctionUtils.accessPathBase(inst.key, method)

        if (currentFact.base == valueBase) {
            val newFact = currentFact.rebase(mapBase).prependAccessor(ElementAccessor)
            result.add(makeEdge(initialFact, newFact))
        }

        if (keyBase != null && currentFact.base == keyBase) {
            val newFact = currentFact.rebase(mapBase).prependAccessor(ElementAccessor)
            result.add(makeEdge(initialFact, newFact))
        }

        return result
    }

    private fun handleSend(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        inst: GoIRSend,
    ): Set<Sequent> {
        val result = mutableSetOf<Sequent>(Sequent.Unchanged)
        val chanBase = GoFlowFunctionUtils.accessPathBase(inst.chan, method)
            ?: return setOf(Sequent.Unchanged)
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.x, method)
            ?: return setOf(Sequent.Unchanged)

        // ch <- x  ==>  ch.element = x (weak update)
        if (currentFact.base == valueBase) {
            val newFact = currentFact.rebase(chanBase).prependAccessor(ElementAccessor)
            result.add(makeEdge(initialFact, newFact))
        }

        return result
    }

    // ── String Concat ────────────────────────────────────────────────

    private fun handleStringConcat(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        registerBase: AccessPathBase,
        expr: GoIRBinOpExpr,
    ): Set<Sequent> {
        val result = mutableSetOf<Sequent>()

        if (currentFact.base == registerBase) {
            // Don't add unchanged — overwritten
        } else {
            result.add(Sequent.Unchanged)
        }

        val leftBase = GoFlowFunctionUtils.accessPathBase(expr.x, method)
        val rightBase = GoFlowFunctionUtils.accessPathBase(expr.y, method)

        if (leftBase != null && currentFact.base == leftBase) {
            result.add(makeEdge(initialFact, currentFact.rebase(registerBase)))
        }
        if (rightBase != null && currentFact.base == rightBase) {
            result.add(makeEdge(initialFact, currentFact.rebase(registerBase)))
        }

        return result
    }

    private fun handleNonPropagatingExpr(
        currentFact: FinalFactAp,
        registerBase: AccessPathBase,
    ): Set<Sequent> {
        return if (currentFact.base == registerBase) {
            emptySet() // register overwritten with clean value
        } else {
            setOf(Sequent.Unchanged)
        }
    }

    private fun applyGlobalOrFieldReadSourceRules(out: MutableSet<Sequent>) {
        val inst = currentInst as? GoIRAssignInst ?: return

        val sourceRules = mutableListOf<TaintRule.GoSourceRule>()

        val fieldName = GoFlowFunctionUtils.detectFieldReadName(inst, method)
        if (fieldName != null) {
            sourceRules += context.taint.taintConfig.sourceRulesForFieldRead(fieldName)
        }

        val globalName = GoFlowFunctionUtils.detectGlobalReadName(inst)
        if (globalName != null) {
            sourceRules += context.taint.taintConfig.sourceRulesForGlobal(globalName)
        }

        if (sourceRules.isEmpty()) return

        val lhv = AccessPathBase.LocalVar(inst.register.index)

        val sourceEvaluator = TaintSourceActionEvaluator(apManager, ExclusionSet.Universe)

        for (rule in sourceRules) {
            if (!rule.condition.isTrue()) {
                TODO("Field/global source with complex condition")
            }

            for (action in rule.actionsAfter) {
                val pos = action.pos.resolvePosAccess()
                val mark = TaintMarkAccessor(action.mark)

                sourceEvaluator.evaluate(rule, action, pos, mark).onSome { evaluatedFacts ->
                    val trace = TraceInfo.Rule(rule, action)

                    evaluatedFacts.mapTo(out) {
                        if (it.base !is AccessPathBase.Return) {
                            TODO("Field/global source with non-result assign")
                        }

                        Sequent.ZeroToFact(it.rebase(lhv), trace)
                    }
                }
            }
        }
    }

    private fun makeEdge(initialFact: InitialFactAp?, newFact: FinalFactAp): Sequent {
        val traceInfo = traceInfoOrNull()
        return if (initialFact != null) {
            val syncedInitial = if (initialFact.exclusions != newFact.exclusions) {
                initialFact.replaceExclusions(newFact.exclusions)
            } else {
                initialFact
            }
            Sequent.FactToFact(syncedInitial, newFact, traceInfo)
        } else {
            Sequent.ZeroToFact(newFact, traceInfo)
        }
    }

    private fun traceInfoOrNull(): TraceInfo? = if (generateTrace) TraceInfo.Flow else null
}
