package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.go.GoFlowFunctionUtils.resolvePosAccess
import org.opentaint.dataflow.taint.PassActionEvaluator
import org.opentaint.util.Maybe

fun <T> PassActionEvaluator<T>.accept(rule: CommonTaintConfigurationItem, action: GoTaintAction): Maybe<List<T>> =
    when (val it = action) {
        is CopyTaintMark -> propagateTaint(
            rule, it,
            it.from.resolvePosAccess(), it.to.resolvePosAccess(),
            TaintMarkAccessor(it.mark)
        )

        is CopyData -> propagateData(
            rule, it,
            it.from.resolvePosAccess(), it.to.resolvePosAccess()
        )

        else -> Maybe.none()
    }
