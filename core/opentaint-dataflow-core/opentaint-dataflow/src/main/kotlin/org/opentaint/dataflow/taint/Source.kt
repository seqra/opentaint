package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.AnyAccessor
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
        if (factReader.containsPositionWithTaintMark(position, mark)) {
            return Maybe.some(listOf(rule to action))
        }

        // Retry with the trailing `[any]` stripped. This is a workaround for premises that could
        // not hold an `[any]`: `AccessPath.AccessNode.addParent` used to drop it, so a source rule
        // whose position ends in `[any]` never matched the premise built for it and the lookup had
        // to fall back to the `[any]`-free prefix.
        //
        // `addParent` no longer drops it, but the workaround must stay until step 5 puts a PRODUCER
        // of `[any]` premises in place: until then the premises reaching this evaluator still come
        // from paths that never introduce an `[any]`, and removing the fallback now would simply
        // lose every such source. Once step 5 lands the exact lookup above succeeds on its own and
        // this branch becomes redundant -- retire it there, not here.
        if (position is PositionAccess.Complex && position.accessor == AnyAccessor) {
            if (factReader.containsPositionWithTaintMark(position.base, mark)) {
                return Maybe.some(listOf(rule to action))
            }
        }

        return Maybe.none()
    }
}
