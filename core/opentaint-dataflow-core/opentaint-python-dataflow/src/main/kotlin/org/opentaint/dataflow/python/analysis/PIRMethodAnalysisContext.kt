package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.python.alias.PIRLocalAliasAnalysis
import org.opentaint.dataflow.python.rules.PIRTaintAnalysisContext
import org.opentaint.dataflow.python.rules.PIRTaintConfiguration
import org.opentaint.ir.api.python.PIRFunction

class PIRMethodAnalysisContext(
    override val methodEntryPoint: MethodEntryPoint,
    val method: PIRFunction,
    val taint: PIRTaintAnalysisContext,
    val taintRules: PIRTaintConfiguration,
    val aliasAnalysis: PIRLocalAliasAnalysis?,
) : MethodAnalysisContext {

    override val methodCallFactMapper: PIRMethodCallFactMapper
        get() = PIRMethodCallFactMapper
}
