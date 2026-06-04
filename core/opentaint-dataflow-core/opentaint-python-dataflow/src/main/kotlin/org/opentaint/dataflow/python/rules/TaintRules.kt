package org.opentaint.dataflow.python.rules

import org.opentaint.dataflow.configuration.CommonTaintRulesProvider
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers

sealed interface TaintRules {
    data class Source(val function: String, val mark: String, val pos: PositionBase) : TaintRules
    data class Sink(val function: String, val mark: String, val pos: PositionBase, val id: String) : TaintRules
    data class Pass(val function: String, val from: PositionBaseWithModifiers, val to: PositionBaseWithModifiers) : TaintRules

    /**
     * Entry source: a function's parameter is assumed tainted at the start of analysis.
     * Used for benchmark tests where the source is an external input parameter.
     * The start flow function creates a ZeroToFact edge for the specified parameter
     * when the current method matches [function].
     */
    data class EntrySource(val function: String, val mark: String, val paramIndex: Int) : TaintRules
}
