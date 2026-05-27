package org.opentaint.dataflow.configuration

import org.opentaint.dataflow.configuration.CommonCondition.And
import org.opentaint.dataflow.configuration.CommonCondition.Atom
import org.opentaint.dataflow.configuration.CommonCondition.Not
import org.opentaint.dataflow.configuration.CommonCondition.Or

interface CommonConditionRewriter<A> : CommonConditionVisitor<A, CommonCondition<A>> {
    fun rewriteAtom(atom: A): A

    override fun visit(condition: Atom<A>): CommonCondition<A> =
        Atom(rewriteAtom(condition.atom))

    override fun visit(condition: CommonCondition.True): CommonCondition<A> = mkTrue()

    override fun visit(condition: Not<A>): CommonCondition<A> =
        Not(condition.arg.accept(this))

    override fun visit(condition: And<A>): CommonCondition<A> =
        mkAnd(condition.args.map { it.accept(this) })

    override fun visit(condition: Or<A>): CommonCondition<A> =
        mkOr(condition.args.map { it.accept(this) })
}
