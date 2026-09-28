package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.TaintCleanReach
import org.opentaint.dataflow.configuration.jvm.RemoveMark
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintCleanActionEvaluator
import org.opentaint.dataflow.taint.EvaluatedCleanAction
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.PositionTypeResolver
import org.opentaint.dataflow.taint.TaintCleanActionEvaluator
import org.opentaint.dataflow.taint.accessors
import org.opentaint.dataflow.taint.base
import org.opentaint.dataflow.taint.hasAnyField

internal class JIRBackwardTaintCleanActionEvaluator(
    private val forward: TaintCleanActionEvaluator = TaintCleanActionEvaluator(),
) {
    fun evaluator(positionTypeResolver: PositionTypeResolver): JIRTaintCleanActionEvaluator =
        JIRTaintCleanActionEvaluator(positionTypeResolver, ::removeFinalFact)

    private fun removeFinalFact(
        evc: EvaluatedCleanAction,
        from: PositionAccess,
        mark: TaintMarkAccessor,
        rule: CommonTaintConfigurationItem,
        action: RemoveMark,
        reach: TaintCleanReach,
    ): List<EvaluatedCleanAction> {
        val cleaned = forward.removeFinalFact(evc, from, mark, rule, action, reach)
        if (reach != TaintCleanReach.Exact || from.hasAnyField()) return cleaned
        if (cleaned.singleOrNull() === evc) return cleaned

        val fact = evc.fact ?: return cleaned
        val anyFieldPart = fact.factAp.anyFieldPartAt(from) ?: return cleaned
        if (cleaned.any { it.fact?.factAp == anyFieldPart }) return cleaned

        val actionInfo = EvaluatedCleanAction.ActionInfo(rule, action)
        return cleaned + EvaluatedCleanAction(fact.replaceFact(anyFieldPart), actionInfo, evc)
    }

    private fun FinalFactAp.anyFieldPartAt(position: PositionAccess): FinalFactAp? {
        if (position.base() != base) return null

        val accessors = position.accessors()
        var node = this
        for (accessor in accessors) {
            node = node.readAccessor(accessor) ?: return null
        }

        val afterAny = node.readAccessor(AnyAccessor) ?: return null
        return accessors.asReversed().fold(afterAny.prependAccessor(AnyAccessor)) { fact, accessor ->
            fact.prependAccessor(accessor)
        }
    }
}
