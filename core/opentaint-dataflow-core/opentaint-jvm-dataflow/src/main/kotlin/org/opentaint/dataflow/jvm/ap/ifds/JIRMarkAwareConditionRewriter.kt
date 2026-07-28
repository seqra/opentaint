package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.jvm.ContainsMark
import org.opentaint.dataflow.configuration.jvm.JirCondition
import org.opentaint.dataflow.configuration.jvm.PositionAccessor
import org.opentaint.dataflow.configuration.jvm.PositionResolver
import org.opentaint.dataflow.configuration.jvm.PositionWithAccess
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.taint.ContainsMarkOnAnyField
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRBasicAtomEvaluator
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.dataflow.taint.RuleConditionRewriter.Companion.falseExpr
import org.opentaint.dataflow.taint.RuleConditionRewriter.Companion.trueExpr
import org.opentaint.dataflow.taint.RuleConditionRewriter.ExprOrConstant
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr
import org.opentaint.ir.api.common.cfg.CommonInst

class JIRMarkAwareConditionRewriter(
    positionResolver: PositionResolver<CallPositionValue>,
    factTypeChecker: JIRFactTypeChecker,
    aliasAnalysis: JIRLocalAliasAnalysis?,
    statement: CommonInst,
): RuleConditionRewriter<JirCondition> {
    private val positiveAtomEvaluator = JIRBasicAtomEvaluator(negated = false, positionResolver, factTypeChecker, aliasAnalysis, statement)
    private val negativeAtomEvaluator = JIRBasicAtomEvaluator(negated = true, positionResolver, factTypeChecker, aliasAnalysis, statement)

    constructor(
        positionResolver: PositionResolver<CallPositionValue>,
        context: JIRMethodAnalysisContext,
        statement: CommonInst
    ) : this(positionResolver, context.factTypeChecker, context.aliasAnalysis, statement)

    override fun rewriteAtom(atom: JirCondition, negated: Boolean): ExprOrConstant {
        if (!negated) {
            return rewriteAtom(atom, positiveAtomEvaluator)
        }

        return rewriteAtom(atom, negativeAtomEvaluator).negate()
    }

    private fun rewriteAtom(atom: JirCondition, evaluator: JIRBasicAtomEvaluator): ExprOrConstant {
        val normalizedAtom = normalizeTrailingAnyField(atom)

        if (normalizedAtom is ContainsMark) {
            return ExprOrConstant(TaintMarkAwareConditionExpr.ContainsMarkLiteral(normalizedAtom.position.resolveAp(), TaintMarkAccessor(normalizedAtom.mark.name), negated = false))
        }

        if (normalizedAtom is ContainsMarkOnAnyField) {
            return ExprOrConstant(TaintMarkAwareConditionExpr.ContainsMarkOnAnyAccessorLiteral(normalizedAtom.position.resolveAp(), TaintMarkAccessor(normalizedAtom.mark.name), negated = false))
        }

        val result = atom.accept(evaluator)
        return if (result) trueExpr else falseExpr
    }

    /**
     * A trailing any-field modifier (`arg(0).*` in a serialized condition) asks whether the mark
     * sits anywhere at or below the position, which is exactly what [ContainsMarkOnAnyField] means,
     * so the serialized form is normalised into it and lowered by the single
     * `ContainsMarkOnAnyAccessorLiteral` construction site above. Lowering it to a plain
     * ContainsMarkLiteral over an AnyAccessor query instead silently matches nothing: an abstract
     * fact reports its read mismatch without an accessor, so the demand-driven refinement that
     * unfolds the fact never fires.
     *
     * Only a TRAILING modifier is normalised: the any-field-ness is carried by the condition type,
     * so the position handed to [ContainsMarkOnAnyField] is the base. A non-trailing any field
     * (`arg(0).*.f`) keeps its accessor chain and falls through to the ContainsMarkLiteral path.
     */
    private fun normalizeTrailingAnyField(atom: JirCondition): JirCondition {
        if (atom !is ContainsMark) return atom

        val position = atom.position
        if (position !is PositionWithAccess || position.access !is PositionAccessor.AnyFieldAccessor) return atom

        return ContainsMarkOnAnyField(position.base, atom.mark)
    }
}
