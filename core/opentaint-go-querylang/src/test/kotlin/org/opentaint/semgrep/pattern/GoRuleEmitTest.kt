package org.opentaint.semgrep.pattern

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.go.rules.GoTaintConfig
import org.opentaint.dataflow.go.rules.TaintRules
import org.opentaint.semgrep.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.go.GoTaintRuleEmitter
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class GoRuleEmitTest {
    private fun emitConfig(resource: String): Pair<GoTaintConfig, GoTaintRuleEmitter> {
        val yaml = javaClass.classLoader.getResource(resource)!!.readText()
        val loader = SemgrepRuleLoader(mapOf("go" to GoLanguageStrategy()))
        loader.registerRuleSet(yaml, Path(resource), Path("."), SemgrepLoadTrace())
        val (meta, rule) = loader.loadGoRules().single()
        val emitter = GoTaintRuleEmitter()
        return emitter.emit(meta.ruleId, rule) to emitter
    }

    @Test fun sourceSinkEmitsExpectedConfig() {
        val (cfg, _) = emitConfig("go-rules/source-sink.yaml")
        assertEquals(listOf(TaintRules.Source("util.Source", "taint", PositionBase.Result)), cfg.sources)
        assertEquals("util.Sink", cfg.sinks.single().function)
        assertEquals(PositionBase.Argument(0), cfg.sinks.single().pos)
    }

    @Test fun passEmitsPropagator() {
        val (cfg, _) = emitConfig("go-rules/pass.yaml")
        assertTrue(cfg.propagators.isNotEmpty(), "expected a propagator")
        assertEquals("util.Wrap", cfg.propagators.single().function)
    }

    @Test fun unsupportedSinkIsDroppedAndCounted() {
        val (cfg, emitter) = emitConfig("go-rules/needs-conditions.yaml")
        // the metavar-named source ($F(...)) should be dropped; the sink still emits
        assertTrue(emitter.dropped.isNotEmpty(), "expected a dropped entry, got: ${emitter.dropped}")
    }
}
