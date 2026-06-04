package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.DummyPositionTypeResolver
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.SELF_ACCESSOR
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.mkFieldAccessor
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.resolveAp
import org.opentaint.dataflow.python.alias.forEachAliasAfterStatement
import org.opentaint.dataflow.python.util.PIRFlowFunctionUtils
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.TaintPassActionEvaluator
import org.opentaint.dataflow.taint.TaintSourceActionEvaluator
import org.opentaint.ir.api.python.*
import org.opentaint.util.onSome
import kotlin.collections.plusAssign

class PIRMethodSequentFlowFunction(
    private val instruction: PIRInstruction,
    private val ctx: PIRMethodAnalysisContext,
    private val apManager: ApManager,
    private val callResolver: PIRCallResolver,
) : MethodSequentFlowFunction {

    private val resolvedNames by lazy { callResolver.resolveNames(instruction) }

    override fun propagateZeroToZero(): Set<Sequent> = buildSet {
        this += Sequent.ZeroToZero

        if (instruction !is PIRLoadAttr) return@buildSet

        val sourceRules = resolvedNames.flatMap { ctx.taintRules.sourcesForAttribute(it) }
        val evaluator = TaintSourceActionEvaluator(apManager, ExclusionSet.Universe)

        sourceRules.forEach { rule ->
            rule.taint.forEach { action ->
                val pos = action.pos.resolveAp() ?: return@forEach
                val mark = TaintMarkAccessor(action.mark.name)

                evaluator.evaluate(rule, action, pos, mark).onSome { facts ->
                    facts.forEach { fact ->
                        ctx.methodCallFactMapper.mapLoadAttributeFactToReturn(instruction, fact)?.let {
                            this += Sequent.ZeroToFact(it, traceInfo = null)
                        }
                    }
                }
            }
        }
    }

    override fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<Sequent> = buildSet {
        propagateFact(
            currentFactAp = currentFactAp,
            unchanged = { this += Sequent.Unchanged },
            propagateFact = { this += Sequent.ZeroToFact(it, null) },
            propagateFactWithAccessorExclude = { _, _ -> error("Zero fact can't carry an accessor exclusion") },
            addSideEffectRequirement = { error("Can't refine Zero fact") },
        )
    }

    override fun propagateFactToFact(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
    ): Set<Sequent> = buildSet {
        propagateFact(
            currentFactAp = currentFactAp,
            unchanged = { this += Sequent.Unchanged },
            propagateFact = { this += Sequent.FactToFact(initialFactAp, it, null) },
            propagateFactWithAccessorExclude = { fact, accessor ->
                // Exclude the accessor on BOTH edge ends so the edge stays well-formed.
                this += Sequent.FactToFact(initialFactAp.exclude(accessor), fact.exclude(accessor), null)
            },
            addSideEffectRequirement = { reader ->
                this += Sequent.SideEffectRequirement(
                    reader.refineFact(initialFactAp.replaceExclusions(ExclusionSet.Empty))
                )
            },
        )
    }

    override fun propagateNDFactToFact(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
    ): Set<Sequent> = setOf(Sequent.Unchanged)

    /**
     * Shared dispatch over the instruction kind. Results are collected by the caller's
     * Unit-returning lambdas (mirrors [PIRMethodCallFlowFunction.propagateFact]).
     */
    private fun propagateFact(
        currentFactAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
    ) {
        when (instruction) {
            is PIRAssign -> handleAssign(
                assign = instruction,
                currentFactAp = currentFactAp,
                unchanged = unchanged,
                propagateFact = propagateFact,
                propagateFactWithAccessorExclude = propagateFactWithAccessorExclude,
            )
            is PIRLoadAttr -> handleAttrRead(
                inst = instruction,
                currentFactAp = currentFactAp,
                unchanged = unchanged,
                propagateFact = propagateFact,
                propagateFactWithAccessorExclude = propagateFactWithAccessorExclude,
                addSideEffectRequirement = addSideEffectRequirement,
            )
            is PIRReturn -> handleReturn(instruction, currentFactAp, unchanged, propagateFact)
            is PIRStoreAttr -> handleStoreAttr(instruction, currentFactAp, unchanged, propagateFact)
            is PIRStoreSubscript -> handleStoreSubscript(instruction, currentFactAp, unchanged, propagateFact)
            else -> unchanged()
        }
    }

    // ==========================================================================
    // Assignment: target = expr
    // ==========================================================================

    /**
     * Assignment `target = expr`. Dispatches based on expression type:
     * - Simple value (PIRValue): variable-to-variable copy
     * - PIRSubscriptExpr: subscript read (x = obj[i])
     * - Container/binary/string: taint flows from operands
     * - Other compound: strong update (kill) on target
     */
    private fun handleAssign(
        assign: PIRAssign,
        currentFactAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor) -> Unit,
    ) {
        val assignTo = PIRFlowFunctionUtils.accessPathBase(assign.target) ?: return unchanged()
        val expr = assign.expr

        // Case 1: Simple value copy (x = y)
        if (expr is PIRValue) {
            val assignFrom = PIRFlowFunctionUtils.accessPathBase(expr)
            if (assignFrom != null) {
                if (currentFactAp.base == assignFrom) {
                    propagateFact(currentFactAp.rebase(assignTo))
                    unchanged() // keep on source too
                } else if (currentFactAp.base == assignTo) {
                    // Strong update: kill fact on overwritten target
                } else {
                    unchanged()
                }
                return
            }
            // Constant or unresolvable value — kill if overwriting target, else pass
            if (currentFactAp.base != assignTo) unchanged()
            return
        }

        // Case 2: Subscript read (x = obj[index])
        if (expr is PIRSubscriptExpr) {
            handleSubscriptRead(expr, assignTo, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
            return
        }

        // Case 3: Container literal (dict, list, tuple, set) — taint flows from values to target
        if (expr is PIRDictExpr || expr is PIRListExpr || expr is PIRTupleExpr || expr is PIRSetExpr) {
            handleContainerLiteral(expr, assignTo, currentFactAp, unchanged, propagateFact)
            return
        }

        // Case 4: Binary expression — taint flows from either operand (e.g. string concatenation)
        if (expr is PIRBinaryExpr) {
            handleBinExpr(expr, assignTo, currentFactAp, unchanged, propagateFact)
            return
        }

        // Case 5: String expression (f-string parts) — taint flows from any part
        if (expr is PIRStringExpr) {
            handleStringExpr(expr, assignTo, currentFactAp, unchanged, propagateFact)
            return
        }

        // Case 6: Other compound expression — strong update on target, pass through otherwise
        if (currentFactAp.base != assignTo) unchanged()
    }

    // ==========================================================================
    // LoadAttr: target = obj.attr (PIRLoadAttr instruction)
    // ==========================================================================

    /**
     * Field read: target = obj.attr
     *
     * If fact is on obj with matching field accessor (e.g., obj.data.![taint].*),
     * read the field accessor to produce target.![taint].* and rebase.
     *
     * If fact is abstract on obj (obj.*) and field is not excluded,
     * materialize the concrete read and propagate the abstract fact with the field
     * excluded on both edge ends.
     */
    private fun handleAttrRead(
        inst: PIRLoadAttr,
        currentFactAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
    ) {
        val assignTo = PIRFlowFunctionUtils.accessPathBase(inst.target) ?: return unchanged()

        val passRulesReader = FinalFactReader(currentFactAp, apManager)
        ctx.methodCallFactMapper.mapLoadAttributeFactToStart(inst, currentFactAp) { fact, newBase ->
            val mappedFact = fact.rebase(newBase)
            applyLoadAttrPassRules(inst, passRulesReader, mappedFact) {
                propagateFact(it)
            }
        }

        if (passRulesReader.hasRefinement) {
            addSideEffectRequirement(passRulesReader)
        }

        val objBase = PIRFlowFunctionUtils.accessPathBase(inst.obj) ?: run {
            if (currentFactAp.base != assignTo) unchanged()
            return
        }
        val accessor = mkFieldAccessor(inst.attribute)

        if (currentFactAp.base == objBase) {
            if (currentFactAp.startsWithAccessor(accessor)) {
                // Concrete: strip the field accessor and rebase
                currentFactAp.readAccessor(accessor)?.rebase(assignTo)?.let { propagateFact(it) }
                // Original fact on obj survives (field read is non-destructive)
                if (assignTo != objBase) {
                    unchanged()
                }
            } else if (currentFactAp.isAbstract() && accessor !in currentFactAp.exclusions) {
                // Abstract: field might be behind *.
                // Materialize: remove abstraction and try concrete read
                val nonAbstract = currentFactAp.removeAbstraction()
                if (nonAbstract != null && nonAbstract.startsWithAccessor(accessor)) {
                    nonAbstract.readAccessor(accessor)?.rebase(assignTo)?.let { propagateFact(it) }
                }
                // Propagate abstract fact with field excluded on both edge ends
                propagateFactWithAccessorExclude(currentFactAp, accessor)
            } else {
                propagateFact(currentFactAp.rebase(assignTo).prependAccessor(SELF_ACCESSOR))
                // Fact on obj but field doesn't match — pass through
                unchanged()
            }
        } else if (currentFactAp.base == assignTo) {
            // Strong update: kill taint on overwritten target
        } else {
            unchanged()
        }
    }

    private fun applyLoadAttrPassRules(
        inst: PIRLoadAttr,
        originalFactReader: FinalFactReader,
        mappedFact: FinalFactAp,
        propagateFact: (FinalFactAp) -> Unit,
    ) {
        val reader = FinalFactReader(mappedFact, apManager)

        val rules = resolvedNames.flatMap { ctx.taintRules.passThroughForAttribute(it) }
        val typeChecker = FactTypeChecker.Dummy
        val evaluator = TaintPassActionEvaluator(
            apManager, typeChecker, reader,
            DummyPositionTypeResolver
        )

        rules.forEach { rule ->
            rule.copy.forEach { action ->
                val from = action.from.resolveAp() ?: return@forEach
                val to = action.to.resolveAp() ?: return@forEach

                evaluator.propagateData(rule, action, from, to).onSome { facts ->
                    facts.forEach { fact ->
                        ctx.methodCallFactMapper.mapLoadAttributeFactToReturn(inst, fact.fact)?.let { mappedFact ->
                            propagateFact(mappedFact)
                        }
                    }
                }
            }
        }

        if (reader.hasRefinement) {
            originalFactReader.updateRefinement(reader)
        }
    }

    /**
     * Subscript read: target = obj[index]
     *
     * Similar to field read but uses ElementAccessor instead of FieldAccessor.
     */
    private fun handleSubscriptRead(
        expr: PIRSubscriptExpr,
        assignTo: AccessPathBase,
        currentFactAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor) -> Unit,
    ) {
        val objBase = PIRFlowFunctionUtils.accessPathBase(expr.obj) ?: run {
            if (currentFactAp.base != assignTo) unchanged()
            return
        }
        val accessor = ElementAccessor

        if (currentFactAp.base == objBase) {
            if (currentFactAp.startsWithAccessor(accessor)) {
                // Concrete: strip element accessor and rebase
                currentFactAp.readAccessor(accessor)?.rebase(assignTo)?.let { propagateFact(it) }
                if (assignTo != objBase) {
                    unchanged()
                }
            } else if (currentFactAp.isAbstract() && accessor !in currentFactAp.exclusions) {
                // Abstract: element might be behind *
                val nonAbstract = currentFactAp.removeAbstraction()
                if (nonAbstract != null && nonAbstract.startsWithAccessor(accessor)) {
                    nonAbstract.readAccessor(accessor)?.rebase(assignTo)?.let { propagateFact(it) }
                }
                // Propagate abstract fact with element excluded on both edge ends
                propagateFactWithAccessorExclude(currentFactAp, accessor)
            } else {
                unchanged()
            }
        } else if (currentFactAp.base == assignTo) {
            // Strong update: kill taint on overwritten target
        } else {
            unchanged()
        }
    }

    // ==========================================================================
    // Container literal: target = {k: v, ...} / [v, ...] / (v, ...) / {v, ...}
    // ==========================================================================

    /**
     * If any value in the container matches the current fact's base, propagate taint
     * to target with ElementAccessor prepended. Dict keys are not tracked.
     */
    private fun handleContainerLiteral(
        expr: PIRExpr,
        assignTo: AccessPathBase,
        currentFactAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
    ) {
        val valueExpressions: List<PIRValue> = when (expr) {
            is PIRDictExpr -> expr.values
            is PIRListExpr -> expr.elements
            is PIRTupleExpr -> expr.elements
            is PIRSetExpr -> expr.elements
            else -> return unchanged()
        }

        for (valueExpr in valueExpressions) {
            val valueBase = PIRFlowFunctionUtils.accessPathBase(valueExpr) ?: continue
            if (currentFactAp.base == valueBase) {
                // Element-level taint (precise)
                val elementFact = currentFactAp.rebase(assignTo)
                    .prependAccessor(ElementAccessor)
                propagateFact(elementFact)
                unchanged()  // value keeps its taint
                return
            }
        }

        // No value matched — strong update if overwriting target, else pass through
        if (currentFactAp.base != assignTo) unchanged()
    }

    // ==========================================================================
    // Binary expression: target = left op right
    // ==========================================================================

    /**
     * For operations like string concatenation (ADD), if either operand is tainted,
     * taint flows to the result. This is a broad rule — conservative but safe.
     */
    private fun handleBinExpr(
        expr: PIRBinaryExpr,
        assignTo: AccessPathBase,
        currentFactAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
    ) {
        val leftBase = PIRFlowFunctionUtils.accessPathBase(expr.left)
        val rightBase = PIRFlowFunctionUtils.accessPathBase(expr.right)

        if ((leftBase != null && currentFactAp.base == leftBase) ||
            (rightBase != null && currentFactAp.base == rightBase)
        ) {
            propagateFact(currentFactAp.rebase(assignTo))
            unchanged()
            return
        }

        // Strong update on overwritten target
        if (currentFactAp.base != assignTo) unchanged()
    }

    // ==========================================================================
    // String expression (f-string parts): target = f"... {part} ..."
    // ==========================================================================

    /**
     * If any string part is tainted, taint flows to the result.
     */
    private fun handleStringExpr(
        expr: PIRStringExpr,
        assignTo: AccessPathBase,
        currentFactAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
    ) {
        for (part in expr.parts) {
            val partBase = PIRFlowFunctionUtils.accessPathBase(part) ?: continue
            if (currentFactAp.base == partBase) {
                propagateFact(currentFactAp.rebase(assignTo))
                unchanged()
                return
            }
        }

        // Strong update on overwritten target
        if (currentFactAp.base != assignTo) unchanged()
    }

    // ==========================================================================
    // Return
    // ==========================================================================

    private fun handleReturn(
        ret: PIRReturn,
        currentFactAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
    ) {
        unchanged()
        val retVal = ret.value ?: return
        val retBase = PIRFlowFunctionUtils.accessPathBase(retVal) ?: return
        if (currentFactAp.base == retBase) {
            propagateFact(currentFactAp.rebase(AccessPathBase.Return))
        }
    }

    // ==========================================================================
    // StoreAttr: obj.attr = value
    // ==========================================================================

    /**
     * obj.attr = value: if fact is on value, propagate taint to obj.attr.
     * Also applies strong update when the current fact is on obj.attr.
     */
    private fun handleStoreAttr(
        store: PIRStoreAttr,
        currentFactAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
    ) {
        val objBase = PIRFlowFunctionUtils.accessPathBase(store.obj) ?: return unchanged()
        val valueBase = PIRFlowFunctionUtils.accessPathBase(store.value)

        if (valueBase != null && currentFactAp.base == valueBase) {
            val accessor = mkFieldAccessor(store.attribute)
            val newFact = currentFactAp.rebase(objBase).prependAccessor(accessor)
            propagateFact(newFact)
            ctx.aliasAnalysis?.forEachAliasAfterStatement(instruction, newFact) { propagateFact(it) }
            unchanged()
            return
        }

        if (currentFactAp.base == objBase && factStartsWithField(currentFactAp, store.attribute)) {
            // Strong update: obj.attr is being overwritten — kill the tainted field fact
            return
        }

        unchanged()
    }

    /**
     * Checks if a fact's access path starts with a FieldAccessor matching the given field name.
     * Uses name-only matching, ignoring className and fieldType (which may vary between instructions).
     */
    private fun factStartsWithField(factAp: FinalFactAp, fieldName: String): Boolean {
        val startAccessors = factAp.getStartAccessors()
        return startAccessors.any { it is FieldAccessor && it.fieldName == fieldName }
    }

    // ==========================================================================
    // StoreSubscript: obj[index] = value
    // ==========================================================================

    /**
     * obj[index] = value: if fact is on value, propagate taint to obj's element.
     * Also applies strong update when the current fact is on obj's element.
     */
    private fun handleStoreSubscript(
        store: PIRStoreSubscript,
        currentFactAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
    ) {
        val objBase = PIRFlowFunctionUtils.accessPathBase(store.obj) ?: return unchanged()
        val valueBase = PIRFlowFunctionUtils.accessPathBase(store.value)

        val accessor = ElementAccessor

        if (valueBase != null && currentFactAp.base == valueBase) {
            val elementFact = currentFactAp.rebase(objBase).prependAccessor(accessor)
            propagateFact(elementFact)
            ctx.aliasAnalysis?.forEachAliasAfterStatement(instruction, elementFact) { propagateFact(it) }
            unchanged()
            return
        }

        if (currentFactAp.base == objBase && currentFactAp.startsWithAccessor(accessor)) {
            // Strong update: element is being overwritten — kill
            return
        }

        unchanged()
    }

    // TODO propagateAbstractFactWithFieldExcluded with aliasing ?
}
