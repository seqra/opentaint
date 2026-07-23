package org.opentaint.dataflow.ap.ifds.trace.action

import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithInterproceduralTrace
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem

sealed interface ActionableRulesCollectionResult {
    data object Failed : ActionableRulesCollectionResult
    data class Collected(val rules: List<Pair<CommonTaintConfigurationItem, CommonTaintAction?>>): ActionableRulesCollectionResult
}

fun TaintAnalysisUnitRunnerManager.collectActionableRules(
    vulnerability: VulnerabilityWithInterproceduralTrace,
): ActionableRulesCollectionResult {
    TODO()
}
