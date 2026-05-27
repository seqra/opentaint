package org.opentaint.dataflow.configuration.jvm

import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.ir.api.jvm.JIRType
import java.util.Objects

typealias Condition = CommonCondition<JirCondition>

interface JirConditionVisitor<out R> {
    fun visit(condition: IsConstant): R
    fun visit(condition: IsNull): R
    fun visit(condition: ConstantEq): R
    fun visit(condition: ConstantLt): R
    fun visit(condition: ConstantGt): R
    fun visit(condition: ConstantMatches): R
    fun visit(condition: ContainsMark): R
    fun visit(condition: TypeMatches): R
    fun visit(condition: TypeMatchesPattern): R
    fun visit(condition: IsStaticField): R
}

interface JirCondition {
    fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R
}

data class IsConstant(
    val position: Position,
) : JirCondition {
    override fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R = conditionVisitor.visit(this)
}

data class IsNull(
    val position: Position,
) : JirCondition {
    override fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R = conditionVisitor.visit(this)
}

data class ConstantEq(
    val position: Position,
    val value: ConstantValue,
) : JirCondition {
    override fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R = conditionVisitor.visit(this)
}

data class ConstantLt(
    val position: Position,
    val value: ConstantValue,
) : JirCondition {
    override fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R = conditionVisitor.visit(this)
}

data class ConstantGt(
    val position: Position,
    val value: ConstantValue,
) : JirCondition {
    override fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R = conditionVisitor.visit(this)
}

data class ConstantMatches(
    val position: Position,
    val pattern: Regex,
) : JirCondition {
    override fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R = conditionVisitor.visit(this)
}

@Suppress("EqualsOrHashCode")
data class ContainsMark(
    val position: Position,
    val mark: TaintMark,
) : JirCondition {
    override fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R = conditionVisitor.visit(this)

    private val hash = Objects.hash(position, mark)
    override fun hashCode(): Int = hash
}

data class TypeMatches(
    val position: Position,
    val type: JIRType,
) : JirCondition {
    override fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R = conditionVisitor.visit(this)
}

sealed interface ConditionNameMatcher {
    sealed interface Simple : ConditionNameMatcher

    data object AnyName: Simple
    data class Concrete(val name: String) : Simple
    data class Pattern(val pattern: Regex) : Simple

    data class PatternEndsWith(val suffix: String) : ConditionNameMatcher
    data class PatternStartsWith(val prefix: String) : ConditionNameMatcher
}

data class TypeMatchesPattern(
    val position: Position,
    val pattern: ConditionNameMatcher,
    val typeArgs: List<TypeArgMatcher>? = null,
) : JirCondition {
    override fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R = conditionVisitor.visit(this)
}

sealed interface ConstantValue

data class ConstantIntValue(val value: Int) : ConstantValue

data class ConstantBooleanValue(val value: Boolean) : ConstantValue

data class ConstantStringValue(val value: String) : ConstantValue

data class IsStaticField(
    val position: Position,
    val className: ConditionNameMatcher,
    val fieldName: ConditionNameMatcher.Simple,
) : JirCondition {
    override fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R = conditionVisitor.visit(this)
}
