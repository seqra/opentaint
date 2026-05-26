package org.opentaint.semgrep.pattern

import org.opentaint.GoTaintRuleEmitter
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.semgrep.pattern.conversion.GoLanguageStrategy
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertTrue

class GoRuleEmitTest {
    private fun emitConfig(resource: String): GoTaintConfiguration {
        val yaml = javaClass.classLoader.getResource(resource)!!.readText()
        val loader = SemgrepRuleLoader(listOf(GoLanguageStrategy()))
        loader.registerRuleSet(yaml, Path(resource), Path("."), SemgrepLoadTrace())
        val loadedRules = loader.loadRules()
        val rule = loadedRules.rulesWithMeta.first()

        @Suppress("UNCHECKED_CAST")
        val firstRule = rule.first as TaintRuleFromSemgrep<GoSerializedItem>
        return GoTaintRuleEmitter().emit(firstRule)
    }

    @Test fun sourceSinkEmitsExpectedConfig() {
        val cfg = emitConfig("go-rules/source-sink.yaml")
        assertTrue(cfg.sourceForFunction("util.Source".signature(0), allRelevant = false).isNotEmpty(), "expected util.Source source")
        assertTrue(cfg.sinkForFunction("util.Sink".signature(1)).isNotEmpty(), "expected util.Sink sink")
    }

    @Test fun needsConditionsEmitsSinkOnly() {
        val cfg = emitConfig("go-rules/needs-conditions.yaml")
        assertTrue(cfg.sinkForFunction("util.Sink".signature(1)).isNotEmpty(), "expected the sink to be emitted")
    }

    fun String.signature(args: Int): GoFunctionSignature =
        GoFunctionSignature(this, receiverType = null, paramTypes = List(args) { "any" }, resultType = "any")
}
