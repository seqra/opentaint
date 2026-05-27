package org.opentaint.dataflow.configuration

interface CommonConditionVisitor<A, out R> {
    fun visit(condition: CommonCondition.True): R
    fun visit(condition: CommonCondition.Atom<A>): R
    fun visit(condition: CommonCondition.Not<A>): R
    fun visit(condition: CommonCondition.And<A>): R
    fun visit(condition: CommonCondition.Or<A>): R
}
