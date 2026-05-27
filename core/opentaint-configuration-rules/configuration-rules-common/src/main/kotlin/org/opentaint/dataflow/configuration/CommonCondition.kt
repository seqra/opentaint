package org.opentaint.dataflow.configuration

sealed interface CommonCondition<A> {
    fun <R> accept(visitor: CommonConditionVisitor<A, R>): R

    data object True : CommonCondition<Nothing> {
        override fun <R> accept(visitor: CommonConditionVisitor<Nothing, R>): R = visitor.visit(this)
    }

    data class Atom<A>(val atom: A) : CommonCondition<A> {
        override fun <R> accept(visitor: CommonConditionVisitor<A, R>): R = visitor.visit(this)
    }

    data class Not<A>(val arg: CommonCondition<A>) : CommonCondition<A> {
        override fun <R> accept(visitor: CommonConditionVisitor<A, R>): R = visitor.visit(this)
    }

    data class And<A>(val args: List<CommonCondition<A>>) : CommonCondition<A> {
        override fun <R> accept(visitor: CommonConditionVisitor<A, R>): R = visitor.visit(this)
    }

    data class Or<A>(val args: List<CommonCondition<A>>) : CommonCondition<A> {
        override fun <R> accept(visitor: CommonConditionVisitor<A, R>): R = visitor.visit(this)
    }
}
