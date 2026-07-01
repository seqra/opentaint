package org.opentaint.semgrep.pattern

import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.ir.go.type.GoIRUnsafePointerType
import org.opentaint.semgrep.go.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.go.pattern.conversion.loadGoTaintConfiguration
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
        return GoTaintConfiguration().loadGoTaintConfiguration(firstRule)
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

    @Test fun patternEitherWithTwoImportInsidesQualifiesBothPackages() {
        val cfg = emitConfig("go-rules/two-import-either.yaml")
        assertTrue(
            cfg.sinkForFunction("html/template.HTMLEscapeString".signature(1)).isNotEmpty(),
            "pattern-either of two pattern-inside imports should yield the html/template variant",
        )
        assertTrue(
            cfg.sinkForFunction("text/template.HTMLEscapeString".signature(1)).isNotEmpty(),
            "pattern-either of two pattern-inside imports should yield the text/template variant",
        )
        assertTrue(
            cfg.sinkForFunction("t.HTMLEscapeString".signature(1)).isEmpty(),
            "the shared alias must not leak into a resolved sink name",
        )
    }

    @Test fun importInPatternInsideQualifiesSiblingPattern() {
        val cfg = emitConfig("go-rules/import-inside.yaml")
        assertTrue(
            cfg.sinkForFunction("os/exec.Command".signature(1)).isNotEmpty(),
            "import declared in pattern-inside should qualify the sibling sink pattern to os/exec.Command",
        )
        assertTrue(
            cfg.sinkForFunction("os/exec.CommandContext".signature(2)).isNotEmpty(),
            "the pattern-inside import should qualify every alternative under pattern-either",
        )
        assertTrue(
            cfg.sinkForFunction("syscall.Exec".signature(1)).isNotEmpty(),
            "multiple imports in one pattern-inside should each qualify their selector",
        )
        assertTrue(
            cfg.sinkForFunction("ex.Command".signature(1)).isEmpty(),
            "the local import alias must not leak into the resolved sink name",
        )
    }

    private val anyType = GoIRUnsafePointerType

    fun String.signature(args: Int): GoFunctionSignature =
        GoFunctionSignature(this, receiverType = null, paramTypes = List(args) { anyType }, resultType = anyType)
}
