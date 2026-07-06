package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.configuration.isTrue
import org.opentaint.dataflow.python.PIRAttrLoadAnyArgumentResolver
import org.opentaint.dataflow.python.PIRAttrLoadAtomEvaluator
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.PIRConditionRewriter
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.DummyPositionTypeResolver
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.SELF_ACCESSOR
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.mayReadAccessor
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.mkFieldAccessor
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.resolveAp
import org.opentaint.dataflow.python.alias.forEachAliasAfterStatement
import org.opentaint.dataflow.python.util.PIRFlowFunctionUtils
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.TaintPassActionEvaluator
import org.opentaint.ir.api.python.PIRAssign
import org.opentaint.ir.api.python.PIRBinaryExpr
import org.opentaint.ir.api.python.PIRDictExpr
import org.opentaint.ir.api.python.PIRExpr
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.api.python.PIRIterExpr
import org.opentaint.ir.api.python.PIRListExpr
import org.opentaint.ir.api.python.PIRLoadAttr
import org.opentaint.ir.api.python.PIRNextIter
import org.opentaint.ir.api.python.PIRReadNameExpr
import org.opentaint.ir.api.python.PIRReturn
import org.opentaint.ir.api.python.PIRSetExpr
import org.opentaint.ir.api.python.PIRSliceExpr
import org.opentaint.ir.api.python.PIRStoreAttr
import org.opentaint.ir.api.python.PIRStoreGlobal
import org.opentaint.ir.api.python.PIRStoreSubscript
import org.opentaint.ir.api.python.PIRStringExpr
import org.opentaint.ir.api.python.PIRSubscriptExpr
import org.opentaint.ir.api.python.PIRTupleExpr
import org.opentaint.ir.api.python.PIRValue
import org.opentaint.util.onSome

class PIRMethodSequentFlowFunction(
    private val instruction: PIRInstruction,
    private val ctx: PIRMethodAnalysisContext,
    private val apManager: ApManager,
    private val callResolver: PIRCallResolver,
) : MethodSequentFlowFunction {
    private val rulesProvider get() = ctx.taint.taintConfig

    private val resolvedNames by lazy {
        check(instruction is PIRLoadAttr) { "Unexpected resolvedNames access on inst: $instruction" }
        callResolver.resolveAttribute(instruction)
    }

    override fun propagateZeroToZero(): Set<Sequent> = buildSet {
        this += Sequent.ZeroToZero

        if (instruction !is PIRLoadAttr) return@buildSet

        applySourceRules(instruction, emptySet(), null, ExclusionSet.Universe,
            createFinalFact = { it, trace ->
                this += Sequent.ZeroToFact(factAp = it, trace)
            },
            createEdge = { initial, it, trace ->
                this += Sequent.FactToFact(initial, it, trace)
            },
            createNDEdge = { initial, it, trace ->
                this += Sequent.NDFactToFact(initial, it, trace)
            }
        )
    }

    override fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<Sequent> = buildSet {
        propagateFact(
            initialFacts = emptySet(),
            currentFactAp = currentFactAp,
            unchanged = { this += Sequent.Unchanged },
            propagateFact = { it, traceInfo -> this += Sequent.ZeroToFact(it, traceInfo) },
            propagateFactWithAccessorExclude = { _, _, _ -> error("Zero fact can't carry an accessor exclusion") },
            addSideEffectRequirement = { error("Can't refine Zero fact") },
            addUnchecked = { this += it }
        )
    }

    override fun propagateFactToFact(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
    ): Set<Sequent> = buildSet {
        propagateFact(
            initialFacts = setOf(initialFactAp),
            currentFactAp = currentFactAp,
            unchanged = { this += Sequent.Unchanged },
            propagateFact = { it, traceInfo -> this += Sequent.FactToFact(initialFactAp, it, traceInfo) },
            propagateFactWithAccessorExclude = { fact, accessor, traceInfo ->
                // Exclude the accessor on BOTH edge ends so the edge stays well-formed.
                this += Sequent.FactToFact(initialFactAp.exclude(accessor), fact.exclude(accessor), traceInfo)
            },
            addSideEffectRequirement = { reader ->
                this += Sequent.SideEffectRequirement(
                    reader.refineFact(initialFactAp.replaceExclusions(ExclusionSet.Empty))
                )
            },
            addUnchecked = { this += it }
        )
    }

    override fun propagateNDFactToFact(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
    ): Set<Sequent> = buildSet {
        propagateFact(
            initialFacts = initialFacts,
            currentFactAp = currentFactAp,
            unchanged = { this += Sequent.Unchanged },
            propagateFact = { it, traceInfo -> this += Sequent.NDFactToFact(initialFacts, it, traceInfo) },
            propagateFactWithAccessorExclude = { _, _, _ -> error("NDF2F edge can't be refined: $currentFactAp") },
            addSideEffectRequirement = { reader ->
                check(!reader.hasRefinement) { "NDF2F edge can't be refined: $currentFactAp" }
            },
            addUnchecked = { this += it }
        )
    }

    /**
     * Shared dispatch over the instruction kind. Results are collected by the caller's
     * Unit-returning lambdas (mirrors [PIRMethodCallFlowFunction.propagateFact]).
     */
    private fun propagateFact(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
        addUnchecked: (Sequent) -> Unit
    ) {
        when (instruction) {
            is PIRAssign -> handleAssign(
                instruction, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude,
            )
            is PIRLoadAttr -> handleAttrRead(
                instruction, initialFacts, currentFactAp, unchanged, propagateFact,
                propagateFactWithAccessorExclude, addSideEffectRequirement, addUnchecked
            )
            is PIRReturn -> handleReturn(instruction, currentFactAp, unchanged, propagateFact)
            is PIRStoreAttr -> handleStoreAttr(instruction, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
            is PIRStoreSubscript -> handleStoreSubscript(instruction, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
            is PIRStoreGlobal -> handleStoreGlobal(instruction, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
            is PIRNextIter -> handleNextIter(
                instruction, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude,
            )
            else -> unchanged(currentFactAp)
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
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit,
    ) {
        val assignTo = PIRFlowFunctionUtils.accessPathBase(assign.target) ?: return unchanged(currentFactAp)
        val expr = assign.expr

        // Simple value copy (x = y)
        if (expr is PIRValue) {
            handleSimpleAssign(expr, assignTo, currentFactAp, unchanged, propagateFact)
            return
        }

        if (expr is PIRIterExpr) {
            handleSimpleAssign(expr.iterable, assignTo, currentFactAp, unchanged, propagateFact)
            return
        }

        // Subscript read (x = obj[index])
        if (expr is PIRSubscriptExpr) {
            handleSubscriptRead(expr, assignTo, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
            return
        }

        if (expr is PIRSliceExpr) {
            handleSliceExpr(expr, assignTo, currentFactAp, unchanged, propagateFact)
            return
        }

        // Container literal (dict, list, tuple, set) — taint flows from values to target
        if (expr is PIRDictExpr || expr is PIRListExpr || expr is PIRTupleExpr || expr is PIRSetExpr) {
            handleContainerLiteral(expr, assignTo, currentFactAp, unchanged, propagateFact)
            return
        }

        // Binary expression — taint flows from either operand (e.g. string concatenation)
        if (expr is PIRBinaryExpr) {
            handleBinExpr(expr, assignTo, currentFactAp, unchanged, propagateFact)
            return
        }

        // String expression (f-string parts) — taint flows from any part
        if (expr is PIRStringExpr) {
            handleStringExpr(expr, assignTo, currentFactAp, unchanged, propagateFact)
            return
        }

        // Global / module read — read ClassStatic.<name> into the target
        if (expr is PIRReadNameExpr) {
            handleReadNameExpr(expr, assignTo, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
            return
        }

        // Other compound expression — strong update on target, pass through otherwise
        if (currentFactAp.base != assignTo) unchanged(currentFactAp)
    }

    private fun handleNextIter(
        nextIter: PIRNextIter,
        currentFactAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit,
    ) {
        val assignTo = PIRFlowFunctionUtils.accessPathBase(nextIter.target) ?: return unchanged(currentFactAp)
        val objBase = PIRFlowFunctionUtils.accessPathBase(nextIter.iterator)
        val accessor = ElementAccessor

        handleAccessorRead(assignTo, objBase, accessor, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
    }

    private fun handleReadNameExpr(
        expr: PIRReadNameExpr,
        assignTo: AccessPathBase,
        currentFactAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit,
    ) {
        val (instance, accessor) = PIRFlowFunctionUtils.globalAccess(expr.ref)
        handleAccessorRead(assignTo, instance, accessor, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
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
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit,
        addSideEffectRequirement: (FinalFactReader) -> Unit,
        addUnchecked: (Sequent) -> Unit
    ) {
        val factReader = FinalFactReader(currentFactAp, apManager)
        applyLoadAttrPassRules(inst, factReader, propagateFact)

        applySourceRules(
            inst, initialFacts, factReader, currentFactAp.exclusions,
            createFinalFact = { it, trace ->
                propagateFact(it, trace)
            },
            createEdge = { initial, it, trace ->
                addUnchecked(Sequent.FactToFact(initial, it, trace))
            },
            createNDEdge = { initial, it, trace ->
                addUnchecked(Sequent.NDFactToFact(initial, it, trace))
            }
        )

        if (factReader.hasRefinement) {
            addSideEffectRequirement(factReader)
        }

        val assignTo = PIRFlowFunctionUtils.accessPathBase(inst.target) ?: return unchanged(currentFactAp)
        val objBase = PIRFlowFunctionUtils.accessPathBase(inst.obj) ?: run {
            if (currentFactAp.base != assignTo) unchanged(currentFactAp)
            return
        }
        val accessor = mkFieldAccessor(inst.attribute)

        handleAccessorRead(assignTo, objBase, accessor, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)

        if (currentFactAp.base == objBase) {
            // method self binding
            propagateFact(currentFactAp.rebase(assignTo).prependAccessor(SELF_ACCESSOR), TraceInfo.Flow)
        }
    }

    private fun applySourceRules(
        inst: PIRLoadAttr,
        initialFacts: Set<InitialFactAp>,
        factReader: FinalFactReader?,
        exclusionSet: ExclusionSet,
        createFinalFact: (FinalFactAp, TraceInfo) -> Unit,
        createEdge: (InitialFactAp, FinalFactAp, TraceInfo) -> Unit,
        createNDEdge: (Set<InitialFactAp>, FinalFactAp, TraceInfo) -> Unit,
    ) {
        val sourceRules = resolvedNames.flatMapTo(mutableListOf()) { attr ->
            rulesProvider.sourcesForAttribute(attr)
        }
        val conditionRewriter = PIRConditionRewriter(PIRAttrLoadAnyArgumentResolver, PIRAttrLoadAtomEvaluator)

        val taintUtil = PIRAttributeLoadTaintUtil(ctx, inst, apManager)
        taintUtil.applySourceRules(
            sourceRules = sourceRules,
            initialFacts = initialFacts,
            conditionRewriter = conditionRewriter,
            factReader = factReader,
            exclusion = exclusionSet,
            createFinalFact = { srcF, trace ->
                createFinalFact(srcF, trace)
            },
            createEdge = { initial, srcF, trace ->
                createEdge(initial, srcF, trace)
            },
            createNDEdge = { initial, srcF, trace ->
                createNDEdge(initial, srcF, trace)
            },
        )
    }

    private fun applyLoadAttrPassRules(
        inst: PIRLoadAttr,
        originalFactReader: FinalFactReader,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
    ) {
        ctx.methodCallFactMapper.mapLoadAttributeFactToStart(inst, originalFactReader.factAp) { fact, newBase ->
            val mappedFact = fact.rebase(newBase)
            val reader = FinalFactReader(mappedFact, apManager)

            val rules = resolvedNames.flatMap { rulesProvider.passThroughForAttribute(it) }
            val typeChecker = FactTypeChecker.Dummy
            val evaluator = TaintPassActionEvaluator(
                apManager, typeChecker, reader,
                DummyPositionTypeResolver
            )

            rules.forEach { rule ->
                check(rule.condition.isTrue()) { "Unexpected attribute pass rule condition: ${rule.condition}" }

                rule.copy.forEach { action ->
                    val from = action.from.resolveAp() ?: return@forEach
                    val to = action.to.resolveAp() ?: return@forEach
                    val traceInfo = TraceInfo.Rule(rule, action)

                    evaluator.propagateData(rule, action, from, to).onSome { facts ->
                        facts.forEach { fact ->
                            ctx.methodCallFactMapper.mapLoadAttributeFactToReturn(inst, fact.fact)?.let { mappedFact ->
                                propagateFact(mappedFact, traceInfo)
                            }
                        }
                    }
                }
            }

            if (reader.hasRefinement) {
                originalFactReader.updateRefinement(reader)
            }
        }
    }

    private fun handleSliceExpr(
        value: PIRSliceExpr,
        assignTo: AccessPathBase,
        currentFactAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
    ) {
        val obj = value.obj ?: return unchanged(currentFactAp)
        handleSimpleAssign(obj, assignTo, currentFactAp, unchanged, propagateFact)
    }

    private fun handleSimpleAssign(
        value: PIRValue,
        assignTo: AccessPathBase,
        currentFactAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
    ) {
        if (currentFactAp.base != assignTo) unchanged(currentFactAp)

        val assignFrom = PIRFlowFunctionUtils.accessPathBase(value) ?: return

        if (assignFrom == assignTo) {
            unchanged(currentFactAp)
            return
        }

        if (currentFactAp.base == assignFrom) {
            propagateFact(currentFactAp.rebase(assignTo), TraceInfo.Flow)
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
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit,
    ) {
        val objBase = PIRFlowFunctionUtils.accessPathBase(expr.obj)
        val accessor = ElementAccessor

        handleAccessorRead(assignTo, objBase, accessor, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
    }

    private fun handleAccessorRead(
        assignTo: AccessPathBase,
        instance: AccessPathBase?,
        accessor: Accessor,
        factAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit
    ) {
        if (assignTo != factAp.base) {
            if (accessor !is ElementAccessor) {
                unchanged(factAp)
            } else {
                propagateFact(factAp, TraceInfo.Flow)
            }
        }

        if (instance == null || !factAp.mayReadAccessor(instance, accessor)) {
            return
        }

        if (factAp.isAbstract() && accessor !in factAp.exclusions) {
            val nonAbstractAp = factAp.removeAbstraction()
            if (nonAbstractAp != null) {
                handleAccessorRead(
                    assignTo, instance, accessor, nonAbstractAp,
                    unchanged, propagateFact, propagateFactWithAccessorExclude
                )
            }

            propagateFactWithAccessorExclude(factAp, accessor, TraceInfo.Flow)

            return
        }

        check(factAp.startsWithAccessor(accessor))

        val newAp = factAp.readAccessor(accessor)?.rebase(assignTo) ?: error("Impossible")
        propagateFact(newAp, TraceInfo.Flow)
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
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
    ) {
        if (currentFactAp.base != assignTo) unchanged(currentFactAp)

        val valueExpressions: List<PIRValue> = when (expr) {
            is PIRDictExpr -> expr.values
            is PIRListExpr -> expr.elements
            is PIRTupleExpr -> expr.elements
            is PIRSetExpr -> expr.elements
            else -> return
        }

        for (elem in valueExpressions) {
            val elemBase = PIRFlowFunctionUtils.accessPathBase(elem)
            if (currentFactAp.base != elemBase) continue

            val elementFact = currentFactAp.rebase(assignTo)
                .prependAccessor(ElementAccessor)

            propagateFact(elementFact, TraceInfo.Flow)
            return
        }
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
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
    ) {
        if (currentFactAp.base != assignTo) unchanged(currentFactAp)

        val leftBase = PIRFlowFunctionUtils.accessPathBase(expr.left)
        val rightBase = PIRFlowFunctionUtils.accessPathBase(expr.right)

        if (currentFactAp.base == leftBase || currentFactAp.base == rightBase) {
            propagateFact(currentFactAp.rebase(assignTo), TraceInfo.Flow)
        }
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
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
    ) {
        if (currentFactAp.base != assignTo) unchanged(currentFactAp)

        for (part in expr.parts) {
            val partBase = PIRFlowFunctionUtils.accessPathBase(part)
            if (currentFactAp.base != partBase) continue

            propagateFact(currentFactAp.rebase(assignTo), TraceInfo.Flow)
            return
        }
    }

    // ==========================================================================
    // Return
    // ==========================================================================

    private fun handleReturn(
        ret: PIRReturn,
        currentFactAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
    ) {
        unchanged(currentFactAp)
        val retVal = ret.value ?: return
        val retBase = PIRFlowFunctionUtils.accessPathBase(retVal) ?: return
        if (currentFactAp.base == retBase) {
            propagateFact(currentFactAp.rebase(AccessPathBase.Return), TraceInfo.Flow)
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
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit
    ) {
        val objBase = PIRFlowFunctionUtils.accessPathBase(store.obj) ?: return unchanged(currentFactAp)
        val valueBase = PIRFlowFunctionUtils.accessPathBase(store.value)
        val accessor = mkFieldAccessor(store.attribute)

        handleAccessorWrite(objBase, accessor, valueBase, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
    }

    private fun handleAccessorWrite(
        destObj: AccessPathBase,
        accessor: Accessor,
        assignFrom: AccessPathBase?,
        currentFactAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit
    ) {
        if (destObj == assignFrom) {
            if (currentFactAp.base != destObj) {
                unchanged(currentFactAp)
                return
            }

            val auxiliaryBase = AccessPathBase.LocalVar.create(-1) // b
            check(auxiliaryBase != destObj)

            handleAccessorWrite(
                destObj = destObj,
                accessor = accessor,
                assignFrom = auxiliaryBase,
                currentFactAp = currentFactAp,
                unchanged = {
                    if (it.base != auxiliaryBase) {
                        unchanged(it)
                    }
                },
                propagateFact = { f, traceInfo ->
                    if (f.base != auxiliaryBase) {
                        propagateFact(f, traceInfo)
                    }
                },
                propagateFactWithAccessorExclude = { f, a, traceInfo ->
                    if (f.base != auxiliaryBase) {
                        propagateFactWithAccessorExclude(f, a, traceInfo)
                    }
                }
            )

            handleAccessorWrite(
                destObj = destObj,
                accessor = accessor,
                assignFrom = auxiliaryBase,
                currentFactAp = currentFactAp.rebase(auxiliaryBase),
                unchanged = {
                    if (it.base != auxiliaryBase) {
                        unchanged(it)
                    }
                },
                propagateFact = { f, traceInfo ->
                    if (f.base != auxiliaryBase) {
                        propagateFact(f, traceInfo)
                    }
                },
                propagateFactWithAccessorExclude = { f, a, traceInfo ->
                    if (f.base != auxiliaryBase) {
                        propagateFactWithAccessorExclude(f, a, traceInfo)
                    }
                }
            )
        }

        if (currentFactAp.base == assignFrom) {
            val newFact = currentFactAp.rebase(destObj).prependAccessor(accessor)
            propagateFact(newFact, TraceInfo.Flow)

            ctx.aliasAnalysis?.forEachAliasAfterStatement(instruction, newFact) {
                propagateFact(it, TraceInfo.Flow)
            }

            unchanged(currentFactAp)
            return
        }

        if (currentFactAp.base != destObj) {
            unchanged(currentFactAp)
            return
        }

        if (accessor is ElementAccessor) {
            // Weak update for elements
            propagateFact(currentFactAp, TraceInfo.Flow)
            return
        }

        if (currentFactAp.isAbstract() && !currentFactAp.exclusions.contains(accessor)) {
            propagateFactWithAccessorExclude(currentFactAp, accessor, TraceInfo.Flow)

            val nonAbstractFact = currentFactAp.removeAbstraction()
            if (nonAbstractFact != null) {
                handleAccessorWrite(
                    destObj, accessor, assignFrom, nonAbstractFact, 
                    unchanged, propagateFact, propagateFactWithAccessorExclude
                )
            }
            return
        }

        if (!currentFactAp.startsWithAccessor(accessor)) {
            propagateFact(currentFactAp, TraceInfo.Flow)
            return
        }

        val cleaned = currentFactAp.clearAccessor(accessor)
        if (cleaned != null) {
            propagateFact(cleaned, TraceInfo.Flow)
        }
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
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit
    ) {
        val objBase = PIRFlowFunctionUtils.accessPathBase(store.obj) ?: return unchanged(currentFactAp)
        val valueBase = PIRFlowFunctionUtils.accessPathBase(store.value)
        val accessor = ElementAccessor

        handleAccessorWrite(objBase, accessor, valueBase, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
    }

    private fun handleStoreGlobal(
        store: PIRStoreGlobal,
        currentFactAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit
    ) {
        val (objBase, accessor) = PIRFlowFunctionUtils.globalAccess(store.ref)
        val valueBase = PIRFlowFunctionUtils.accessPathBase(store.value)

        handleAccessorWrite(objBase, accessor, valueBase, currentFactAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
    }

    // TODO propagateAbstractFactWithFieldExcluded with aliasing ?
}
