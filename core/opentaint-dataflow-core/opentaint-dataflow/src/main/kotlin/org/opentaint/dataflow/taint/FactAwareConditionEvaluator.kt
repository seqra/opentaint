package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

interface FactAwareConditionEvaluator {
    fun evalWithAssumptionsCheck(condition: TaintMarkAwareConditionExpr): Boolean
    fun assumptionExpr(): TaintMarkAwareConditionExpr?
    fun facts(): List<InitialFactAp>
}
