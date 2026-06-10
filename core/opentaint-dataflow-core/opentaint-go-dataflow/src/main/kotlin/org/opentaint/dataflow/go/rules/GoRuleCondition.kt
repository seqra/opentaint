package org.opentaint.dataflow.go.rules

sealed interface GoRuleCondition {
    fun <R> accept(visitor: GoConditionVisitor<R>): R

    data class ContainsMark(val position: Position, val mark: String) : GoRuleCondition {
        override fun <R> accept(visitor: GoConditionVisitor<R>): R = visitor.visit(this)
    }

    data class ContainsMarkOnAnyAccessor(val position: Position, val mark: String) : GoRuleCondition {
        override fun <R> accept(visitor: GoConditionVisitor<R>): R = visitor.visit(this)
    }

    data class IsConstant(val position: Position.Simple) : GoRuleCondition {
        override fun <R> accept(visitor: GoConditionVisitor<R>): R = visitor.visit(this)
    }

    data class IsNull(val position: Position.Simple) : GoRuleCondition {
        override fun <R> accept(visitor: GoConditionVisitor<R>): R = visitor.visit(this)
    }

    data class ConstantEq(val position: Position.Simple, val value: ConstantValue) : GoRuleCondition {
        override fun <R> accept(visitor: GoConditionVisitor<R>): R = visitor.visit(this)
    }

    data class ConstantLt(val position: Position.Simple, val value: ConstantValue) : GoRuleCondition {
        override fun <R> accept(visitor: GoConditionVisitor<R>): R = visitor.visit(this)
    }

    data class ConstantGt(val position: Position.Simple, val value: ConstantValue) : GoRuleCondition {
        override fun <R> accept(visitor: GoConditionVisitor<R>): R = visitor.visit(this)
    }

    data class ConstantMatches(val position: Position.Simple, val pattern: Regex) : GoRuleCondition {
        override fun <R> accept(visitor: GoConditionVisitor<R>): R = visitor.visit(this)
    }
}

interface GoConditionVisitor<out R> {
    fun visit(c: GoRuleCondition.ContainsMark): R
    fun visit(c: GoRuleCondition.ContainsMarkOnAnyAccessor): R
    fun visit(c: GoRuleCondition.IsConstant): R
    fun visit(c: GoRuleCondition.IsNull): R
    fun visit(c: GoRuleCondition.ConstantEq): R
    fun visit(c: GoRuleCondition.ConstantLt): R
    fun visit(c: GoRuleCondition.ConstantGt): R
    fun visit(c: GoRuleCondition.ConstantMatches): R
}

sealed interface ConstantValue

data class ConstantIntValue(val value: Int) : ConstantValue
data class ConstantStringValue(val value: String) : ConstantValue
data class ConstantBooleanValue(val value: Boolean) : ConstantValue
