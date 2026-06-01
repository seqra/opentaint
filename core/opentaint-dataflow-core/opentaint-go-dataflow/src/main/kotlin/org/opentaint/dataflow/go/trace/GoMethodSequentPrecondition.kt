package org.opentaint.dataflow.go.trace

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition
import org.opentaint.dataflow.configuration.isTrue
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access
import org.opentaint.dataflow.go.GoFlowFunctionUtils.resolvePosAccess
import org.opentaint.dataflow.go.analysis.GoMethodAnalysisContext
import org.opentaint.dataflow.go.rules.TaintRule
import org.opentaint.dataflow.taint.InitialFactReader
import org.opentaint.dataflow.taint.TaintSourceActionPreconditionEvaluator
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.expr.GoIRBinOpExpr
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.inst.GoIRMapUpdate
import org.opentaint.ir.go.inst.GoIRPhi
import org.opentaint.ir.go.inst.GoIRReturn
import org.opentaint.ir.go.inst.GoIRSend
import org.opentaint.ir.go.inst.GoIRStore
import org.opentaint.ir.go.type.GoIRBinaryOp
import org.opentaint.util.maybeFlatMap

class GoMethodSequentPrecondition(
    private val apManager: ApManager,
    private val currentInst: GoIRInst,
    private val analysisContext: GoMethodAnalysisContext,
) : MethodSequentPrecondition {

    private val method: GoIRFunction get() = analysisContext.method

    override fun factPrecondition(fact: InitialFactAp): Set<SequentPrecondition> {
        val result = hashSetOf<SequentPrecondition>()
        addPreconditions(fact, result)
        if (result.isEmpty()) result += SequentPrecondition.Unchanged
        return result
    }

    private fun addPreconditions(fact: InitialFactAp, result: MutableSet<SequentPrecondition>) {
        when (val inst = currentInst) {
            is GoIRAssignInst -> {
                result.unconditionalGlobalOrFieldReadSourceRulePrecondition(inst, fact)
                handleAssign(inst, fact, result)
            }
            is GoIRStore -> handleStore(inst, fact, result)
            is GoIRReturn -> handleReturn(inst, fact, result)
            is GoIRPhi -> handlePhi(inst, fact, result)
            is GoIRMapUpdate -> handleMapUpdate(inst, fact, result)
            is GoIRSend -> handleSend(inst, fact, result)
            else -> Unit
        }
    }

    private fun MutableSet<SequentPrecondition>.addUnchanged() {
        this += SequentPrecondition.Unchanged
    }

    private fun MutableSet<SequentPrecondition>.addPreFact(target: InitialFactAp, pre: InitialFactAp) {
        this += PreconditionFactsForInitialFact(target, listOf(pre))
    }

    private fun MutableSet<SequentPrecondition>.addPreFacts(target: InitialFactAp, pres: List<InitialFactAp>) {
        this += PreconditionFactsForInitialFact(target, pres)
    }

    private fun MutableSet<SequentPrecondition>.addKill(target: InitialFactAp) {
        this += PreconditionFactsForInitialFact(target, emptyList())
    }

    private fun handleAssign(inst: GoIRAssignInst, fact: InitialFactAp, result: MutableSet<SequentPrecondition>) {
        val registerBase = AccessPathBase.LocalVar(inst.register.index)
        val expr = inst.expr

        if (expr is GoIRBinOpExpr && expr.op == GoIRBinaryOp.ADD
            && GoFlowFunctionUtils.isStringType(expr.type)
        ) {
            handleStringConcatPrecondition(fact, registerBase, expr, result)
            return
        }

        val rhsAccess = GoFlowFunctionUtils.exprToAccess(expr, method)
        if (rhsAccess == null) {
            handleNonPropagatingPrecondition(fact, registerBase, result)
            return
        }

        when (rhsAccess) {
            is Access.Simple -> handleSimpleAssignPrecondition(fact, registerBase, rhsAccess.base, result)
            is Access.RefAccess -> handleRefAssignPrecondition(fact, registerBase, rhsAccess, result)
        }
    }

    private fun handleSimpleAssignPrecondition(
        fact: InitialFactAp,
        toBase: AccessPathBase,
        fromBase: AccessPathBase,
        result: MutableSet<SequentPrecondition>,
    ) {
        if (fact.base == toBase) {
            // Fact lives on the destination after assignment.
            if (fromBase == toBase) return // unchanged
            result.addPreFact(fact, fact.rebase(fromBase))
            return
        }
        // Fact is unrelated to the destination — unchanged.
    }

    private fun handleRefAssignPrecondition(
        fact: InitialFactAp,
        toBase: AccessPathBase,
        rhsAccess: Access.RefAccess,
        result: MutableSet<SequentPrecondition>,
    ) {
        if (fact.base != toBase) {
            // unchanged
            return
        }

        val newFact = fact.prependAccessor(rhsAccess.accessor).rebase(rhsAccess.base)
        result.addPreFact(fact, newFact)
    }

    // ── Store ────────────────────────────────────────────────────────

    private fun handleStore(inst: GoIRStore, fact: InitialFactAp, result: MutableSet<SequentPrecondition>) {
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method) ?: return
        val addrAccess = GoFlowFunctionUtils.accessForAddr(inst.addr, method) ?: return

        when (addrAccess) {
            is Access.RefAccess -> {
                val destBase = addrAccess.base
                val accessor = addrAccess.accessor

                if (fact.base != destBase) return // unchanged

                if (!fact.startsWithAccessor(accessor)) {
                    // The store wrote to `accessor`, but the fact is at a different accessor
                    // of the same base — pass through.
                    return
                }

                val stripped = fact.readAccessor(accessor) ?: return
                val genFact = stripped.rebase(valueBase)

                if (accessor is ElementAccessor) {
                    // Weak update on container element. There are two possibilities for
                    // the post-fact: (a) it was generated by the stored value; (b) it
                    // pre-existed (preserved through the weak update).
                    //
                    // We always emit the gen case as a Pre. We additionally emit
                    // [SequentPrecondition.Unchanged] when the value cannot itself be a
                    // useful taint source (e.g. a literal constant). Emitting Unchanged
                    // lets the edge searcher and the main resolver walk past statements
                    // where the fact merely passes through (since the analyzer does not
                    // record unchanged edges in its lookup DB).
                    //
                    // When the value IS a real taint source candidate (a register or
                    // parameter), we must NOT emit Unchanged: doing so would cause the
                    // searcher to walk past this gen point and miss the recorded edge at
                    // the immediately-following statement.
                    val valueIsTaintSource = valueBase !is AccessPathBase.Constant
                    if (valueIsTaintSource) {
                        result.addPreFacts(fact, listOf(genFact, fact))
                    } else {
                        result.addUnchanged()
                        result.addPreFact(fact, genFact)
                    }
                } else {
                    // Strong update: fact under `accessor` must come from the stored value.
                    result.addPreFact(fact, genFact)
                }
            }

            is Access.Simple -> {
                val destBase = addrAccess.base
                if (fact.base != destBase) return // unchanged
                result.addPreFact(fact, fact.rebase(valueBase))
            }
        }
    }

    private fun handleReturn(inst: GoIRReturn, fact: InitialFactAp, result: MutableSet<SequentPrecondition>) {
        if (fact.base !is AccessPathBase.Return) return

        if (inst.results.size == 1) {
            val retBase = GoFlowFunctionUtils.accessPathBase(inst.results[0], method) ?: return
            result.addPreFact(fact, fact.rebase(retBase))
            return
        }

        val pres = mutableListOf<InitialFactAp>()
        for ((i, retVal) in inst.results.withIndex()) {
            val retBase = GoFlowFunctionUtils.accessPathBase(retVal, method) ?: continue
            val tupleAccessor: Accessor = GoFlowFunctionUtils.tupleFieldAccessor(i, retVal.type)
            if (!fact.startsWithAccessor(tupleAccessor)) continue
            val stripped = fact.readAccessor(tupleAccessor) ?: continue
            pres += stripped.rebase(retBase)
        }
        if (pres.isNotEmpty()) result.addPreFacts(fact, pres)
    }

    private fun handlePhi(inst: GoIRPhi, fact: InitialFactAp, result: MutableSet<SequentPrecondition>) {
        val registerBase = AccessPathBase.LocalVar(inst.register.index)
        if (fact.base != registerBase) return

        val pres = mutableListOf<InitialFactAp>()
        for (edge in inst.edges.values) {
            val edgeBase = GoFlowFunctionUtils.accessPathBase(edge, method) ?: continue
            pres += fact.rebase(edgeBase)
        }
        if (pres.isNotEmpty()) result.addPreFacts(fact, pres)
    }

    private fun handleMapUpdate(inst: GoIRMapUpdate, fact: InitialFactAp, result: MutableSet<SequentPrecondition>) {
        val mapBase = GoFlowFunctionUtils.accessPathBase(inst.map, method) ?: return
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method) ?: return

        if (fact.base != mapBase) return
        if (!fact.startsWithAccessor(ElementAccessor)) return

        val stripped = fact.readAccessor(ElementAccessor) ?: return
        // Weak update on map element — see [handleStore] for the rationale of choosing
        // between (Unchanged + Pre[gen]) and (Pre[gen, fact]) based on whether the value
        // can itself be a taint source.
        val genFact = stripped.rebase(valueBase)
        if (valueBase is AccessPathBase.Constant) {
            result.addUnchanged()
            result.addPreFact(fact, genFact)
        } else {
            result.addPreFacts(fact, listOf(genFact, fact))
        }
    }

    private fun handleSend(inst: GoIRSend, fact: InitialFactAp, result: MutableSet<SequentPrecondition>) {
        val chanBase = GoFlowFunctionUtils.accessPathBase(inst.chan, method) ?: return
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.x, method) ?: return

        if (fact.base != chanBase) return
        if (!fact.startsWithAccessor(ElementAccessor)) return

        val stripped = fact.readAccessor(ElementAccessor) ?: return
        // Weak update on channel.element — symmetrical to map update.
        val genFact = stripped.rebase(valueBase)
        if (valueBase is AccessPathBase.Constant) {
            result.addUnchanged()
            result.addPreFact(fact, genFact)
        } else {
            result.addPreFacts(fact, listOf(genFact, fact))
        }
    }

    private fun MutableSet<SequentPrecondition>.unconditionalGlobalOrFieldReadSourceRulePrecondition(
        inst: GoIRAssignInst,
        fact: InitialFactAp,
    ) {
        val lhv = AccessPathBase.LocalVar(inst.register.index)
        if (fact.base != lhv) return

        val sourceRules = mutableListOf<TaintRule.GoSourceRule>()

        val fieldName = GoFlowFunctionUtils.detectFieldReadName(inst, method)
        if (fieldName != null) {
            sourceRules += analysisContext.taint.taintConfig.sourceRulesForFieldRead(fieldName)
        }

        val globalName = GoFlowFunctionUtils.detectGlobalReadName(inst, method)
        if (globalName != null) {
            sourceRules += analysisContext.taint.taintConfig.sourceRulesForGlobal(globalName)
        }

        if (sourceRules.isEmpty()) return

        val entryFactReader = InitialFactReader(fact.rebase(AccessPathBase.Return), apManager)
        val sourcePreconditionEvaluator = TaintSourceActionPreconditionEvaluator(entryFactReader)

        for (rule in sourceRules) {
            if (!rule.condition.isTrue()) {
                TODO("Field/global source with complex condition")
            }
            val assignedMarks = rule.actionsAfter.maybeFlatMap { action ->
                sourcePreconditionEvaluator.evaluate(
                    rule, action,
                    action.pos.resolvePosAccess(),
                    TaintMarkAccessor(action.mark),
                )
            }
            if (assignedMarks.isNone) continue
            val sourceActions = assignedMarks.getOrThrow().mapTo(hashSetOf()) { it.second }

            this += MethodSequentPrecondition.SequentSource(
                fact, TaintRulePrecondition.Source(rule, sourceActions)
            )
        }
    }

    private fun handleStringConcatPrecondition(
        fact: InitialFactAp,
        registerBase: AccessPathBase,
        expr: GoIRBinOpExpr,
        result: MutableSet<SequentPrecondition>,
    ) {
        if (fact.base != registerBase) return

        val pres = mutableListOf<InitialFactAp>()
        GoFlowFunctionUtils.accessPathBase(expr.x, method)?.let { pres += fact.rebase(it) }
        GoFlowFunctionUtils.accessPathBase(expr.y, method)?.let { pres += fact.rebase(it) }
        if (pres.isNotEmpty()) result.addPreFacts(fact, pres)
    }

    private fun handleNonPropagatingPrecondition(
        fact: InitialFactAp,
        registerBase: AccessPathBase,
        result: MutableSet<SequentPrecondition>,
    ) {
        if (fact.base == registerBase) {
            // Register overwritten with clean value — fact cannot have any precondition here.
            result.addKill(fact)
        }
    }
}
