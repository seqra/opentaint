package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink

typealias RuleId = CommonTaintConfigurationSink

/** The exact REACH or TAINT part on which one sink literal holds. */
class SinkEdge(val premise: PremiseKey, val layer: Layer, val facts: Facts) {
    init {
        check(facts !is FlowTree) { "A sink edge cannot hold FLOW facts" }
    }
}
