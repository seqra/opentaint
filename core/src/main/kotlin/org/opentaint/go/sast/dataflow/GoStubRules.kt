package org.opentaint.go.sast.dataflow

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.go.rules.GoTaintConfig
import org.opentaint.dataflow.go.rules.TaintRules

/**
 * Predefined, in-code Go taint source/sink rules.
 *
 * Rule loading from external config/files is intentionally NOT implemented (out
 * of scope). These stub rules let the Go SAST pipeline run end-to-end with a
 * fixed rule set. The defaults target the functions defined by the Go test
 * samples (`test/util.Source` / `test/util.Sink`).
 */
object GoStubRules {
    const val TAINT_MARK: String = "taint"

    const val SINK_RULE_ID: String = "go-taint-sink"

    /** Default source: a function returning tainted data (Result position). */
    val defaultSources: List<TaintRules.Source> = listOf(
        TaintRules.Source("test/util.Source", TAINT_MARK, PositionBase.Result),
    )

    /** Default sink: a function whose first argument must not be tainted. */
    val defaultSinks: List<TaintRules.Sink> = listOf(
        TaintRules.Sink("test/util.Sink", TAINT_MARK, PositionBase.Argument(0), SINK_RULE_ID),
    )

    fun defaultConfig(
        sources: List<TaintRules.Source> = defaultSources,
        sinks: List<TaintRules.Sink> = defaultSinks,
        propagators: List<TaintRules.Pass> = emptyList(),
    ): GoTaintConfig = GoTaintConfig(sources, sinks, propagators)
}
