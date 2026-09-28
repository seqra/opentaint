package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.jvm.ap.ifds.JIRFactTypeChecker
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodCallFactMapper
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.mkAccessPath
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.ext.cfg.callExpr

data class JIRBackwardEndRequirement(
    val position: PositionAccess,
    val mark: TaintMarkAccessor,
    val fact: FinalFactAp,
) {
    val analysisEndOnly: Boolean get() = fact.base is AccessPathBase.ClassStatic

    companion object {
        fun of(
            apManager: ApManager,
            factTypeChecker: JIRFactTypeChecker,
            rule: TaintConfigurationSink,
            statement: JIRInst,
        ): JIRBackwardEndRequirement? {
            if (rule.trackFactsReachAnalysisEnd.isEmpty()) return null

            val isCall = statement.callExpr != null
            val requirements = hashMapOf<FinalFactAp, JIRBackwardEndRequirement>()
            for (action in rule.trackFactsReachAnalysisEnd) {
                val position = action.position.resolveAp()
                val mark = TaintMarkAccessor(action.mark.name)
                val fact = apManager.mkAccessPath(position, ExclusionSet.Universe, mark)
                val mapped = if (isCall) {
                    JIRMethodCallFactMapper.mapMethodExitToReturnFlowFact(statement, fact, factTypeChecker).singleOrNull()
                } else {
                    fact
                } ?: continue

                requirements.putIfAbsent(mapped, JIRBackwardEndRequirement(position.rebase(mapped.base), mark, mapped))
            }

            return requirements.values.singleOrNull()
        }

        private fun PositionAccess.rebase(base: AccessPathBase): PositionAccess = when (this) {
            is PositionAccess.Simple -> PositionAccess.Simple(base)
            is PositionAccess.Complex -> PositionAccess.Complex(this.base.rebase(base), accessor)
        }
    }
}
