package org.opentaint.semgrep

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.go.analysis.GoAnalysisManager
import org.opentaint.dataflow.go.graph.GoApplicationGraph
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.jvm.sast.dataflow.DummySerializationContext
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.toGoTaintConfiguration
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.go.config.GoConfigLoader
import org.opentaint.util.analysis.ApplicationGraph
import java.io.File
import java.nio.file.Path
import kotlin.io.path.Path
import kotlin.test.assertTrue
import kotlin.test.fail
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds

/**
 * Sample-driven end-to-end test for Go taint rules.
 *
 * Convention: `core/opentaint-go-querylang/samples-go/<RuleName>/` contains:
 *   - `go.mod`                     — a small Go module (typically `module util`)
 *   - exactly one `*.yaml` rule    — the semgrep rule under test
 *   - one or more `*.go` files     — the test fixture, with top-level functions
 *                                    named `Positive_*` (must report ≥1 vulnerability
 *                                    when used as entrypoint) and `Negative_*`
 *                                    (must report 0).
 *
 * The pipeline mirrors [org.opentaint.go.sast.dataflow.GoSemgrepReachabilityTest] but
 * generalizes the source/entrypoint/sink layout: each [Positive_*]/[Negative_*]
 * top-level function in the sample's Go module becomes an independent
 * analysis run.
 *
 * GoIRProgram build results are cached per sample directory across @Test
 * methods (PER_CLASS lifecycle + companion cache) so subsequent runs don't
 * pay the SSA-server cost again.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GoSampleBasedTest {

    private val samplesDir: Path by lazy {
        val prop = System.getProperty("GO_SAMPLES_DIR")
            ?: error("System property GO_SAMPLES_DIR not set; check build.gradle.kts wiring")
        Path(prop).also {
            require(it.toFile().isDirectory) { "GO_SAMPLES_DIR is not a directory: $it" }
        }
    }

    private val client: GoIRClient by lazy { GoIRClient() }
    private val programCache = mutableMapOf<Path, GoIRProgram>()

    @AfterAll
    fun tearDown() {
        client.close()
    }

    @Test fun simpleSourceSink() = runSample("SimpleSourceSink")

    @Test fun passThrough() = runSample("PassThrough")

    @Test fun sanitizer() = runSample("Sanitizer")

    @Test fun multiArgSink() = runSample("MultiArgSink")

    @Test fun interprocSink() = runSample("InterprocSink")

    @Test fun ellipsisSourceSink() = runSample("EllipsisSourceSink")

    @Test fun constantNotTainted() = runSample("ConstantNotTainted")

    @Test fun nilCheck() = runSample("NilCheck")

    @Test fun multipleSourcesOneSink() = runSample("MultipleSourcesOneSink")

    @Disabled // todo: Fix IsType matching
    @Test fun typeBasedSink() = runSample("TypeBasedSink")

    // ─── Ports of example.* Java sample tests ───────────────────────────────

    @Test fun javaRule() = runSample("JavaRule")

    @Test fun javaRuleWithEllipsisMethodInvocation() = runSample("JavaRuleWithEllipsisMethodInvocation")

    @Test fun javaRuleWithPatternInside() = runSample("JavaRuleWithPatternInside")

    @Test fun javaRuleWithNotInsidePrefix() = runSample("JavaRuleWithNotInsidePrefix")

    @Test fun javaRuleWithNotInsideSuffix() = runSample("JavaRuleWithNotInsideSuffix")

    @Test fun javaRuleWithIntersection() = runSample("JavaRuleWithIntersection")

    @Test fun javaRuleWithSimplePass() = runSample("JavaRuleWithSimplePass")

    @Test fun javaRuleWithSeveralSuffixCleaners() = runSample("JavaRuleWithSeveralSuffixCleaners")

    @Test fun javaRuleReturnSimple() = runSample("JavaRuleReturnSimple")

    @Test fun javaRuleReturnConditional() = runSample("JavaRuleReturnConditional")

    @Test fun javaRuleReturnNotInside() = runSample("JavaRuleReturnNotInside")

    @Test fun javaRuleWithAllowedConstant() = runSample("JavaRuleWithAllowedConstant")

    @Test fun javaRuleWithMultiplePatterns() = runSample("JavaRuleWithMultiplePatterns")

    @Test fun javaCleanerAfterSink1() = runSample("JavaCleanerAfterSink1")

    @Test fun javaRuleWithoutPattern() = runSample("JavaRuleWithoutPattern")

    @Test fun javaR1() = runSample("JavaR1")

    @Test fun javaR2() = runSample("JavaR2")

    @Test fun javaR3() = runSample("JavaR3")

    @Test fun javaNdRule() = runSample("JavaNDRule")

    @Test fun javaRuleReturn1() = runSample("JavaRuleReturn1")

    @Test fun javaRuleReturn2() = runSample("JavaRuleReturn2")

    @Test fun javaRuleReturn4() = runSample("JavaRuleReturn4")

    @Test fun javaRuleReturn5() = runSample("JavaRuleReturn5")

    @Test fun javaRuleReturn6() = runSample("JavaRuleReturn6")

    @Test fun javaTrickyPatternNot() = runSample("JavaTrickyPatternNot")

    @Test fun javaCleanerAfterSink0() = runSample("JavaCleanerAfterSink0")

    @Test fun javaCleanerAfterSink2() = runSample("JavaCleanerAfterSink2")

    @Test fun javaRuleReturnChained() = runSample("JavaRuleReturnChained")

    @Test fun javaRuleReturnNotInsidePrefix() = runSample("JavaRuleReturnNotInsidePrefix")

    @Test fun javaRuleReturnMultiInsideNotInsideA() = runSample("JavaRuleReturnMultiInsideNotInsideA")

    @Test fun javaRuleReturnMultiInsideNotInsideC() = runSample("JavaRuleReturnMultiInsideNotInsideC")

    @Test fun javaRuleReturnInsideSignature() = runSample("JavaRuleReturnInsideSignature")

    @Test fun javaRuleReturnInsideSignature2() = runSample("JavaRuleReturnInsideSignature2")

    @Test fun javaRulePatternNotInsideWithSignature() = runSample("JavaRulePatternNotInsideWithSignature")

    @Test fun javaRulePatternNotWithSignature() = runSample("JavaRulePatternNotWithSignature")

    @Test fun javaRuleReturnWithNotInsideSignature() = runSample("JavaRuleReturnWithNotInsideSignature")

    @Test fun javaRuleWithSignature() = runSample("JavaRuleWithSignature")

    @Test fun javaRuleWithPatternsSignature() = runSample("JavaRuleWithPatternsSignature")

    @Test fun javaRuleWithPatternsSimple() = runSample("JavaRuleWithPatternsSimple")

    @Test fun javaRuleWithRealInsideSequence() = runSample("JavaRuleWithRealInsideSequence")

    @Test fun javaRuleWithArtificialInsideSequence() = runSample("JavaRuleWithArtificialInsideSequence")

    @Test fun javaRuleWithArtificialInsideSequenceReverse() = runSample("JavaRuleWithArtificialInsideSequenceReverse")

    @Test fun javaRuleWithMultiplePatternsUnification() = runSample("JavaRuleWithMultiplePatternsUnification")

    @Test fun javaRuleWithMultiplePatternsEllipsisUnification() = runSample("JavaRuleWithMultiplePatternsEllipsisUnification")

    @Test fun javaRuleWithType() = runSample("JavaRuleWithType")

    @Test fun javaRuleWithEllipsisInvocationAndPatternNot() = runSample("JavaRuleWithEllipsisInvocationAndPatternNot")

    @Test fun javaRuleRequiringCarefulCleaners() = runSample("JavaRuleRequiringCarefulCleaners")

    @Test fun javaRuleWithAnyPattern() = runSample("JavaRuleWithAnyPattern")

    @Test fun javaRuleWithState() = runSample("JavaRuleWithState")

    @Test fun javaRuleRequiringCarefulCleanersInTaint() = runSample("JavaRuleRequiringCarefulCleanersInTaint")

    @Test fun javaRuleWithNotInsideDistinctReturnType() = runSample("JavaRuleWithNotInsideDistinctReturnType")

    @Test fun javaJoinWithTaintAndMatchingLeft() = runSample("JavaJoinWithTaintAndMatchingLeft")

    @Test fun javaArrayExample() = runSample("JavaArrayExample")

    @Test fun javaRuleWithConcreteReturnType() = runSample("JavaRuleWithConcreteReturnType")

    @Test fun javaRuleWithConcreteReturnDiscrim() = runSample("JavaRuleWithConcreteReturnDiscrim")

    @Test fun javaRuleWithMixedMetavarConcrete() = runSample("JavaRuleWithMixedMetavarConcrete")

    @Test fun javaRuleWithDeepNesting() = runSample("JavaRuleWithDeepNesting")

    // ─── Plumbing ───────────────────────────────────────────────────────────

    private fun runSample(ruleName: String, useDefaultConfig: Boolean = false) {
        val sampleDir = samplesDir.resolve(ruleName)
        require(sampleDir.toFile().isDirectory) {
            "Sample directory missing: $sampleDir"
        }

        val program = programCache.getOrPut(sampleDir) {
            client.buildFromDir(sampleDir, GoIRLoadConfig()).program
        }

        val yamlFile = sampleDir.toFile().listFiles { f -> f.extension == "yaml" }
            ?.singleOrNull()
            ?: fail("Expected exactly one *.yaml rule under $sampleDir")
        val config = loadConfig(yamlFile)
        if (useDefaultConfig) {
            val defaultConfig = GoConfigLoader.getConfig()
                ?: fail("Bundled go-config not found on classpath")
            config.loadConfig(defaultConfig)
        }

        val entries = program.allFunctions().filter {
            it.pkg?.importPath == "util" &&
                !it.isSynthetic &&
                it.hasBody &&
                (it.name.startsWith("Positive_") || it.name.startsWith("Negative_"))
        }

        check(entries.isNotEmpty()) {
            "No Positive_*/Negative_* top-level entry points found in $sampleDir " +
                "(seen: ${program.allFunctions().map { it.fullName }})"
        }

        for (entry in entries) {
            val vulns = runAnalysis(program, config, entry)
            val isPositive = entry.name.startsWith("Positive_")
            if (isPositive) {
                assertTrue(
                    vulns.isNotEmpty(),
                    "[$ruleName] Positive entry ${entry.fullName} did not report any vulnerability",
                )
            } else {
                assertTrue(
                    vulns.isEmpty(),
                    "[$ruleName] Negative entry ${entry.fullName} reported vulnerabilities: $vulns",
                )
            }
        }
    }

    private fun loadConfig(yamlFile: File): GoTaintConfiguration {
        val yaml = yamlFile.readText()
        val loader = SemgrepRuleLoader(listOf(GoLanguageStrategy()))
        loader.registerRuleSet(yaml, Path(yamlFile.name), Path("."), SemgrepLoadTrace())
        val loadedRules = loader.loadRules()
        val rule = loadedRules.rulesWithMeta.firstOrNull()
            ?: fail("No rules loaded from $yamlFile")

        @Suppress("UNCHECKED_CAST")
        val typed = rule.first as TaintRuleFromSemgrep<GoSerializedItem>
        return typed.toGoTaintConfiguration()
    }

    private fun runAnalysis(
        program: GoIRProgram,
        config: GoTaintConfiguration,
        entryPoint: GoIRFunction,
    ): List<*> {
        val ifdsGraph = GoApplicationGraph(program, UtilUnitResolver)

        @Suppress("UNCHECKED_CAST")
        val engine = TaintAnalysisUnitRunnerManager(
            GoAnalysisManager(program, config),
            ifdsGraph as ApplicationGraph<CommonMethod, CommonInst>,
            unitResolver = UtilUnitResolver as UnitResolver<CommonMethod>,
            apManager = TreeApManager(anyAccessorUnrollStrategy = AnyAccessorUnrollStrategy.AnyAccessorDisabled),
            summarySerializationContext = DummySerializationContext,
            taintRulesStatsSamplingPeriod = null,
        )

        val startMethod = MethodWithContext(entryPoint, EmptyMethodContext)
        return engine.use { eng ->
            eng.runAnalysis(listOf(startMethod), timeout = 1.minutes, cancellationTimeout = 10.seconds)
            eng.getVulnerabilities()
        }
    }

    private object UtilUnitResolver : UnitResolver<GoIRFunction> {
        override fun resolve(method: GoIRFunction): UnitType =
            when (method.pkg?.importPath) {
                "util" -> SingletonUnit
                else -> UnknownUnit
            }
    }
}
