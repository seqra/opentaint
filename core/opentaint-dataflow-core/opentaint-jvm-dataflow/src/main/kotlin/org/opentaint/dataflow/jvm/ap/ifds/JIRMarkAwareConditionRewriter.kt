package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.jvm.ContainsMark
import org.opentaint.dataflow.configuration.jvm.JirCondition
import org.opentaint.dataflow.configuration.jvm.PositionResolver
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
        if (atom is ContainsMark) {
            return ExprOrConstant(TaintMarkAwareConditionExpr.ContainsMarkLiteral(atom.position.resolveAp(), TaintMarkAccessor(atom.mark.name), negated = false))
        }

        if (atom is ContainsMarkOnAnyField) {
            return ExprOrConstant(TaintMarkAwareConditionExpr.ContainsMarkOnAnyAccessorLiteral(atom.position.resolveAp(), TaintMarkAccessor(atom.mark.name), negated = false))
        }

        val result = atom.accept(evaluator)
        return if (result) trueExpr else falseExpr
    }
}
