package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.configuration.CommonTaintAssignAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.util.Maybe

interface SourceActionEvaluator<T> {
    fun evaluate(rule: CommonTaintConfigurationItem, action: CommonTaintAssignAction, position: PositionAccess, mark: TaintMarkAccessor): Maybe<List<T>>
}

class TaintSourceActionEvaluator(
    private val apManager: ApManager,
    private val exclusion: ExclusionSet,
) : SourceActionEvaluator<FinalFactAp> {
    override fun evaluate(
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAssignAction,
        position: PositionAccess,
        mark: TaintMarkAccessor
    ): Maybe<List<FinalFactAp>> {
         val fact = apManager.mkAccessPath(position, exclusion, mark)
        return Maybe.from(listOf(fact))
    }
}

class TaintSourceActionPreconditionEvaluator(
    private val factReader: InitialFactReader,
) : SourceActionEvaluator<Pair<CommonTaintConfigurationItem, CommonTaintAssignAction>> {
    override fun evaluate(
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAssignAction,
        position: PositionAccess,
        mark: TaintMarkAccessor
    ): Maybe<List<Pair<CommonTaintConfigurationItem, CommonTaintAssignAction>>> {
        if (!factReader.containsPositionWithTaintMark(position, mark)) return Maybe.none()
        return Maybe.some(listOf(rule to action))
    }
}
