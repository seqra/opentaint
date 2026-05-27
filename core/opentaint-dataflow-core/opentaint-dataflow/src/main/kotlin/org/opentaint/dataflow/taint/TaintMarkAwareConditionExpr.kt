package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr.And
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr.Literal
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr.Or
import org.opentaint.dataflow.util.cartesianProductMapTo

sealed interface TaintMarkAwareConditionExpr {
    class And(val args: Array<TaintMarkAwareConditionExpr>) : TaintMarkAwareConditionExpr {
        override fun toString(): String = "And(${args.contentToString()})"

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is And) return false
            return args.contentEquals(other.args)
        }

        override fun hashCode(): Int = args.contentHashCode()
    }

    class Or(val args: Array<TaintMarkAwareConditionExpr>) : TaintMarkAwareConditionExpr {
        override fun toString(): String = "Or(${args.contentToString()})"

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Or) return false
            return args.contentEquals(other.args)
        }

        override fun hashCode(): Int = args.contentHashCode()
    }

    sealed interface Literal : TaintMarkAwareConditionExpr {
        val negated: Boolean
        fun negate(): Literal
    }

    data class ContainsMarkLiteral(val position: PositionAccess, val mark: TaintMarkAccessor, override val negated: Boolean) : Literal {
        override fun negate() = copy(negated = !negated)
    }

    data class ContainsMarkOnAnyAccessorLiteral(val position: PositionAccess, val mark: TaintMarkAccessor, override val negated: Boolean) : Literal {
        override fun negate() = copy(negated = !negated)
    }
}

fun TaintMarkAwareConditionExpr.removeTrueLiterals(
    evalLiteral: (Literal) -> Boolean
): TaintMarkAwareConditionExpr? = removeTrueLiteralsFromExpr(this, evalLiteral)

private fun removeTrueLiteralsFromExpr(
    expr: TaintMarkAwareConditionExpr,
    evalLiteral: (Literal) -> Boolean
) = when (expr) {
    is Literal -> if (evalLiteral(expr)) null else expr
    is And -> removeTrueLiteralsFromAndExpr(expr, evalLiteral)
    is Or -> removeTrueLiteralsFromOrExpr(expr, evalLiteral)
}

private fun removeTrueLiteralsFromAndExpr(expr: And, evalLiteral: (Literal) -> Boolean): TaintMarkAwareConditionExpr? {
    return removeTrueLiteralsFromArray(
        expr.args, { removeTrueLiteralsFromExpr(it, evalLiteral) }, TaintMarkAwareConditionExpr::And,
        createDefault = { return null },
        processElement = { it }
    )
}

private fun removeTrueLiteralsFromOrExpr(expr: Or, evalLiteral: (Literal) -> Boolean): TaintMarkAwareConditionExpr? {
    return removeTrueLiteralsFromArray(
        expr.args, { removeTrueLiteralsFromExpr(it, evalLiteral) }, TaintMarkAwareConditionExpr::Or,
        createDefault = { error("impossible") },
        processElement = { it ?: return null }
    )
}

private inline fun removeTrueLiteralsFromArray(
    elements: Array<TaintMarkAwareConditionExpr>,
    removeTrueLiteralsFromExpr: (TaintMarkAwareConditionExpr) -> TaintMarkAwareConditionExpr?,
    create: (Array<TaintMarkAwareConditionExpr>) -> TaintMarkAwareConditionExpr,
    createDefault: () -> TaintMarkAwareConditionExpr?,
    processElement: (TaintMarkAwareConditionExpr?) -> TaintMarkAwareConditionExpr?,
): TaintMarkAwareConditionExpr? {
    val result = arrayOfNulls<TaintMarkAwareConditionExpr>(elements.size)
    var size = 0
    for (i in elements.indices) {
        val elementResult = removeTrueLiteralsFromExpr(elements[i])
        val elementExpr = processElement(elementResult) ?: continue
        result[size++] = elementExpr
    }

    if (size == 0) {
        return createDefault()
    }

    if (size == 1) {
        return result[0]
    }

    val resultExprs = result.copyOf(size)

    @Suppress("UNCHECKED_CAST")
    resultExprs as Array<TaintMarkAwareConditionExpr>

    return create(resultExprs)
}

data class TaintMarkAwareCube(val literals: Set<Literal>)

fun TaintMarkAwareConditionExpr.explodeToDNF(): List<TaintMarkAwareCube> = when (this) {
    is Literal -> listOf(TaintMarkAwareCube(setOf(this)))
    is Or -> args.flatMap { it.explodeToDNF() }
    is And -> {
        val result = mutableListOf<TaintMarkAwareCube>()
        val cubeLists = args.map { it.explodeToDNF() }
        cubeLists.cartesianProductMapTo { cubes ->
            val literals = hashSetOf<Literal>()
            cubes.flatMapTo(literals) { it.literals }
            result += TaintMarkAwareCube(literals)
        }
        result
    }
}
