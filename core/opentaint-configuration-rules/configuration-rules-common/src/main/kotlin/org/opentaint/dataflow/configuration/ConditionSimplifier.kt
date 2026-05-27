package org.opentaint.dataflow.configuration

import org.opentaint.dataflow.configuration.CommonCondition.And
import org.opentaint.dataflow.configuration.CommonCondition.Not
import org.opentaint.dataflow.configuration.CommonCondition.Or

private class ConditionSimplifierImpl<A> : CommonConditionVisitor<A, CommonCondition<A>> {
    override fun visit(condition: And<A>): CommonCondition<A> {
        val queue = ArrayDeque(condition.args)
        val args = mutableListOf<CommonCondition<A>>()
        while (queue.isNotEmpty()) {
            val it = queue.removeFirst().accept(this)
            if (it is CommonCondition.True) {
                // skip
            } else if (it.isFalse()) {
                return mkFalse()
            } else if (it is And) {
                queue += it.args
            } else {
                args += it
            }
        }
        return mkAnd(args)
    }

    override fun visit(condition: Or<A>): CommonCondition<A> {
        val queue = ArrayDeque(condition.args)
        val args = mutableListOf<CommonCondition<A>>()
        while (queue.isNotEmpty()) {
            val it = queue.removeFirst().accept(this)
            if (it is CommonCondition.True) {
                return mkTrue()
            } else if (it.isFalse()) {
                // skip
            } else if (it is Or) {
                queue += it.args
            } else {
                args += it
            }
        }
        return mkOr(args)
    }

    override fun visit(condition: Not<A>): CommonCondition<A> {
        val arg = condition.arg.accept(this)
        return if (arg is Not) {
            // Eliminate double negation:
            arg.arg
        } else {
            Not(arg)
        }
    }

    override fun visit(condition: CommonCondition.True): CommonCondition<A> = mkTrue()

    override fun visit(condition: CommonCondition.Atom<A>): CommonCondition<A> = condition
}

private val conditionSimplifier = ConditionSimplifierImpl<Nothing>()

@Suppress("UNCHECKED_CAST")
fun <A> conditionSimplifier(): CommonConditionVisitor<A, CommonCondition<A>> =
    conditionSimplifier as CommonConditionVisitor<A, CommonCondition<A>>

@Suppress("UNCHECKED_CAST")
fun <A> mkTrue(): CommonCondition<A> =
    CommonCondition.True as CommonCondition<A>

fun <A> mkFalse(): CommonCondition<A> = Not(mkTrue())

fun <A> mkOr(conditions: List<CommonCondition<A>>) = when (conditions.size) {
    0 -> mkFalse()
    1 -> conditions.single()
    else -> Or(conditions)
}

fun <A> mkAnd(conditions: List<CommonCondition<A>>) = when (conditions.size) {
    0 -> mkTrue()
    1 -> conditions.single()
    else -> And(conditions)
}

fun <A> CommonCondition<A>.simplify(): CommonCondition<A> =
    accept(conditionSimplifier()).toNnf(negated = false)

fun <A> CommonCondition<A>.toNnf(negated: Boolean): CommonCondition<A> = when (this) {
    is Not -> arg.toNnf(!negated)

    is And -> if (!negated) {
        mkAndCondition(args) { it.toNnf(negated = false) }
    } else {
        mkOrCondition(args) { it.toNnf(negated = true) }
    }

    is Or -> if (!negated) {
        mkOrCondition(args) { it.toNnf(negated = false) }
    } else {
        mkAndCondition(args) { it.toNnf(negated = true) }
    }

    else -> if (negated) Not(this) else this
}

inline fun <A> mkOrCondition(
    args: List<CommonCondition<A>>,
    op: (CommonCondition<A>) -> CommonCondition<A>
): Or<A> {
    val result = mutableListOf<CommonCondition<A>>()
    for (arg in args) {
        val mappedArg = op(arg)
        if (mappedArg is Or) {
            result.addAll(mappedArg.args)
        } else {
            result.add(mappedArg)
        }
    }
    return Or(result)
}

inline fun <A> mkAndCondition(
    args: List<CommonCondition<A>>,
    op: (CommonCondition<A>) -> CommonCondition<A>
): And<A> {
    val result = mutableListOf<CommonCondition<A>>()
    for (arg in args) {
        val mappedArg = op(arg)
        if (mappedArg is And) {
            result.addAll(mappedArg.args)
        } else {
            result.add(mappedArg)
        }
    }
    return And(result)
}

fun <A> CommonCondition<A>.isTrue() = this is CommonCondition.True

fun <A> CommonCondition<A>.isFalse() = this is Not && this.arg is CommonCondition.True
