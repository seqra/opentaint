package org.opentaint.dataflow.taint

import org.opentaint.dataflow.configuration.CommonCondition

interface RuleConditionRewriter<A> {
    fun rewriteAtom(atom: A, negated: Boolean): ExprOrConstant

    fun rewrite(condition: CommonCondition<A>): ExprOrConstant = when (condition) {
        is CommonCondition.Atom -> rewriteAtom(condition.atom, negated = false)
        is CommonCondition.And -> rewriteAndCondition(condition.args)
        is CommonCondition.Or -> rewriteOrCondition(condition.args)
        is CommonCondition.Not -> rewriteNotCondition(condition.arg)
        is CommonCondition.True -> trueExpr
    }

    fun rewriteAndCondition(conditionArgs: List<CommonCondition<A>>): ExprOrConstant {
        return rewriteList(conditionArgs, trueExpr, TaintMarkAwareConditionExpr::And) {
            when {
                it.isTrue -> null
                it.isFalse -> return falseExpr
                else -> it.expr
            }
        }
    }

    fun rewriteOrCondition(conditionArgs: List<CommonCondition<A>>): ExprOrConstant {
        return rewriteList(conditionArgs, falseExpr, TaintMarkAwareConditionExpr::Or) {
            when {
                it.isTrue -> return trueExpr
                it.isFalse -> null
                else -> it.expr
            }
        }
    }

    fun rewriteNotCondition(condition: CommonCondition<A>): ExprOrConstant {
        if (condition is CommonCondition.True) return falseExpr

        check(condition is CommonCondition.Atom) { "NNF condition expected" }
        return rewriteAtom(condition.atom, negated = true)
    }

    fun TaintMarkAwareConditionExpr.negate(): TaintMarkAwareConditionExpr = when (this) {
        is TaintMarkAwareConditionExpr.Literal -> negate()
        is TaintMarkAwareConditionExpr.And,
        is TaintMarkAwareConditionExpr.Or -> error("Unexpected formula structure")
    }

    private inline fun rewriteList(
        elements: List<CommonCondition<A>>,
        default: ExprOrConstant,
        create: (Array<TaintMarkAwareConditionExpr>) -> TaintMarkAwareConditionExpr,
        processElement: (ExprOrConstant) -> TaintMarkAwareConditionExpr?,
    ): ExprOrConstant {
        val result = arrayOfNulls<TaintMarkAwareConditionExpr>(elements.size)
        var size = 0
        for (i in elements.indices) {
            val elementResult = rewrite(elements[i])
            val elementExpr = processElement(elementResult) ?: continue
            result[size++] = elementExpr
        }

        if (size == 0) {
            return default
        }

        if (size == 1) {
            return ExprOrConstant(result[0]!!)
        }

        val resultExprs = result.copyOf(size)

        @Suppress("UNCHECKED_CAST")
        resultExprs as Array<TaintMarkAwareConditionExpr>

        return ExprOrConstant(create(resultExprs))
    }

    @JvmInline
    value class ExprOrConstant(private val rawValue: Any?) {
        val isTrue: Boolean get() = rawValue === trueMarker
        val isFalse: Boolean get() = rawValue === falseMarker

        val expr: TaintMarkAwareConditionExpr get() = rawValue as TaintMarkAwareConditionExpr
    }

    fun ExprOrConstant.negate(): ExprOrConstant = when {
        this.isFalse -> trueExpr
        this.isTrue -> falseExpr
        else -> ExprOrConstant(expr.negate())
    }

    object Unconditional : RuleConditionRewriter<Unit> {
        override fun rewriteAtom(atom: Unit, negated: Boolean): ExprOrConstant {
            error("Unconditional condition expected")
        }
    }

    companion object {
        private val trueMarker = Any()
        private val falseMarker = Any()

        val trueExpr = ExprOrConstant(trueMarker)
        val falseExpr = ExprOrConstant(falseMarker)
    }
}
