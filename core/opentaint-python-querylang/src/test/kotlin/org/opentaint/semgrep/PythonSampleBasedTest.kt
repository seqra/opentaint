package org.opentaint.semgrep

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.DummySerializationContext
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonRule
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintConfig
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.python.analysis.PIRAnalysisManager
import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.dataflow.python.rules.PIRConfigTaintRulesProvider
import org.opentaint.dataflow.python.rules.PIRTaintConfiguration
import org.opentaint.dataflow.python.rules.PIRTaintRulesProvider
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.python.PIRClass
import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRClasspathLoader
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.PythonLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.toSerializedPythonTaintConfig
import org.opentaint.util.analysis.ApplicationGraph
import java.io.File
import java.nio.file.Path
import kotlin.io.path.Path
import kotlin.io.path.absolutePathString
import kotlin.test.Ignore
import kotlin.test.assertTrue
import kotlin.test.fail
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds

/**
 * Sample-driven end-to-end test for Python taint rules — Python mirror of
 * [org.opentaint.semgrep.GoSampleBasedTest].
 *
 * Convention: `core/opentaint-python-querylang/samples-py/<RuleName>/` contains:
 *   - `rule.yaml`   — the semgrep rule under test (matching or taint mode)
 *   - `sample.py`   — the fixture, with functions named `Positive_*` (must report
 *                     ≥1 vulnerability when used as entrypoint) and `Negative_*`
 *                     (must report 0).
 *
 * Each sample is built into its own [PIRClasspath] (every file is named `sample.py`,
 * so they cannot share a classpath — the module name would collide). Classpaths are
 * cached per sample dir across @Test methods (PER_CLASS lifecycle) and closed in
 * [tearDown].
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class PythonSampleBasedTest {

    private val samplesDir: Path by lazy {
        val prop = System.getProperty("PY_SAMPLES_DIR")
            ?: error("System property PY_SAMPLES_DIR not set; check build.gradle.kts wiring")
        Path(prop).also {
            require(it.toFile().isDirectory) { "PY_SAMPLES_DIR is not a directory: $it" }
        }
    }

    private val cpCache = mutableMapOf<Path, PIRClasspath>()

    @AfterAll
    fun tearDown() {
        cpCache.values.forEach { it.close() }
        cpCache.clear()
    }

    @Test fun multiArgSink() = runSample("MultiArgSink")
    @Test fun constantArgSink() = runSample("ConstantArgSink")
    @Test fun complexSourceSink() = runSample("ComplexSourceSink")
    @Test fun joinWithTaintAndMatchingLeft() = runSample("JoinWithTaintAndMatchingLeft")
    @Test fun ndRule() = runSample("NDRule")
    @Test fun r3() = runSample("R3")
    @Test fun rule() = runSample("Rule")
    @Test fun ruleRequiringCarefulCleaners() = runSample("RuleRequiringCarefulCleaners")
    @Test fun ruleRequiringCarefulCleanersInTaint() = runSample("RuleRequiringCarefulCleanersInTaint")
    @Test fun ruleWithAllowedConstant() = runSample("RuleWithAllowedConstant")
    @Test fun allowedSpecificConstant() = runSample("AllowedSpecificConstant")
    @Test fun ruleWithArtificialInsideSequence() = runSample("RuleWithArtificialInsideSequence")
    @Test fun ruleWithIntersection() = runSample("RuleWithIntersection")
    @Test fun ruleWithMultiplePatterns() = runSample("RuleWithMultiplePatterns")
    @Test fun ruleWithNotInsidePrefix() = runSample("RuleWithNotInsidePrefix")
    @Test fun ruleWithFirstParamToSink() = runSample("RuleWithFirstParamToSink")
    @Test fun ruleWithSecondParamToSink() = runSample("RuleWithSecondParamToSink")
    @Test fun ruleWithPatternInside() = runSample("RuleWithPatternInside")
    @Test fun ruleWithPatternsSignature() = runSample("RuleWithPatternsSignature")
    @Test fun ruleWithPatternsSimple() = runSample("RuleWithPatternsSimple")
    @Test fun ruleWithRealInsideSequence() = runSample("RuleWithRealInsideSequence")
    @Test fun ruleWithSignature() = runSample("RuleWithSignature")
    @Test fun ruleWithSimplePass() = runSample("RuleWithSimplePass")
    @Test fun ruleWithState() = runSample("RuleWithState")
    @Test fun objectMapperPatternNotEllipsis() = runSample("ObjectMapperPatternNotEllipsis")
    @Test fun objectMapperPatternNotFull() = runSample("ObjectMapperPatternNotFull")
    @Test fun ruleWithArtificialInsideSequenceReverse() = runSample("RuleWithArtificialInsideSequenceReverse")

    @Test fun rulePatternNotInsideWithSignature() = runSample("RulePatternNotInsideWithSignature")
    @Test fun taintRule() = runSample("TaintRule")
    @Test fun complexSourceSinkNoFocus() = runSample("ComplexSourceSinkNoFocus")
    @Test fun ruleNoFocus() = runSample("RuleNoFocus")
    @Test fun ruleNoMeta() = runSample("RuleNoMeta")
    @Test fun ruleWithInside() = runSample("RuleWithInside")
    @Test fun ruleWithPass() = runSample("RuleWithPass")

    // must-aa is required for cleaner to kill all the facts
    @Ignore @Test fun ruleCookie() = runSample("RuleCookie")

    // cleaner after sink
    @Ignore @Test fun cleanerAfterSink0() = runSample("CleanerAfterSink0")
    @Ignore @Test fun cleanerAfterSink1() = runSample("CleanerAfterSink1")
    @Ignore @Test fun cleanerAfterSink2() = runSample("CleanerAfterSink2")
    @Ignore @Test fun ruleWithSeveralSuffixCleaners() = runSample("RuleWithSeveralSuffixCleaners")
    @Ignore @Test fun ruleWithNotInsideSuffix() = runSample("RuleWithNotInsideSuffix")
    @Ignore @Test fun rulePatternNotWithSignature() = runSample("RulePatternNotWithSignature")

    // method-chain ellipsis
    @Ignore @Test fun ruleWithEllipsisInvocationAndPatternNot() = runSample("RuleWithEllipsisInvocationAndPatternNot")
    @Ignore @Test fun ruleWithEllipsisMethodInvocation() = runSample("RuleWithEllipsisMethodInvocation")
    @Ignore @Test fun ruleWithMultiplePatternsEllipsisUnification() = runSample("RuleWithMultiplePatternsEllipsisUnification")

    // return sinks
    @Ignore @Test fun r1() = runSample("R1")
    @Ignore @Test fun r2() = runSample("R2")
    @Ignore @Test fun ruleReturn3() = runSample("RuleReturn3")
    @Ignore @Test fun ruleReturn1() = runSample("RuleReturn1")
    @Ignore @Test fun ruleReturn2() = runSample("RuleReturn2")
    @Ignore @Test fun ruleReturn4() = runSample("RuleReturn4")
    @Ignore @Test fun ruleReturn5() = runSample("RuleReturn5")
    @Ignore @Test fun ruleReturnConditional() = runSample("RuleReturnConditional")
    @Ignore @Test fun ruleReturnInsideSignature() = runSample("RuleReturnInsideSignature")
    @Ignore @Test fun ruleReturnInsideSignature2() = runSample("RuleReturnInsideSignature2")
    @Ignore @Test fun ruleReturnMultiInsideNotInsideA() = runSample("RuleReturnMultiInsideNotInsideA")
    @Ignore @Test fun ruleReturnMultiInsideNotInsideC() = runSample("RuleReturnMultiInsideNotInsideC")
    @Ignore @Test fun ruleReturnSimple() = runSample("RuleReturnSimple")
    @Ignore @Test fun ruleReturnWithNotInsideSignature() = runSample("RuleReturnWithNotInsideSignature")
    @Ignore @Test fun ruleReturnWithNotInsideSignatureWithPass() = runSample("RuleReturnWithNotInsideSignatureWithPass")
    @Ignore @Test fun ruleWithMultiplePatternsUnification() = runSample("RuleWithMultiplePatternsUnification")
    @Ignore @Test fun trickyPatternNot() = runSample("TrickyPatternNot")

    // chained method calls and return sinks
    @Ignore @Test fun ruleReturnChained() = runSample("RuleReturnChained")
    @Ignore @Test fun ruleReturnNotInside() = runSample("RuleReturnNotInside")
    @Ignore @Test fun ruleReturnNotInsidePrefix() = runSample("RuleReturnNotInsidePrefix")

    @Ignore("Return cleaners are not supported")
    @Test fun ruleReturn6() = runSample("RuleReturn6")

    @Ignore("Globals are not supported")
    @Test fun ruleWithStaticField() = runSample("RuleWithStaticField")

    // ─── Plumbing ───────────────────────────────────────────────────────────

    private fun runSample(ruleName: String) {
        val sampleDir = samplesDir.resolve(ruleName)
        require(sampleDir.toFile().isDirectory) { "Sample directory missing: $sampleDir" }

        val cp = cpCache.getOrPut(sampleDir) { buildCp(sampleDir) }

        val yamlFile = sampleDir.toFile().listFiles { f -> f.extension == "yaml" }
            ?.singleOrNull()
            ?: fail("Expected exactly one *.yaml rule under $sampleDir")
        val config = loadConfig(yamlFile)

        val module = cp.findModuleOrNull("sample")
            ?: fail("[$ruleName] module 'sample' not found in classpath")
        val entries = (module.functions + module.classes.flatMap { it.allMethods() })
            .filter { it.name.startsWith("Positive_") || it.name.startsWith("Negative_") }

        check(entries.isNotEmpty()) {
            "[$ruleName] No Positive_*/Negative_* entry points found in $sampleDir"
        }

        for (entry in entries) {
            val vulns = runAnalysis(cp, config, entry)
            val isPositive = entry.name.startsWith("Positive_")
            if (isPositive) {
                assertTrue(
                    vulns.isNotEmpty(),
                    "[$ruleName] Positive entry ${entry.qualifiedName} did not report any vulnerability",
                )
            } else {
                val fpReason = entry.taintRuleFalsePositiveReason()
                if (vulns.isNotEmpty() && fpReason != null) {
                    System.err.println(
                        "[$ruleName] Skip known false-positive negative ${entry.qualifiedName}: $fpReason"
                    )
                } else {
                    assertTrue(
                        vulns.isEmpty(),
                        "[$ruleName] Negative entry ${entry.qualifiedName} reported vulnerabilities: $vulns",
                    )
                }
            }
        }
    }

    /** Reason from a `@TaintRuleFalsePositive("...")` decorator on the entry, or null. */
    private fun PIRFunction.taintRuleFalsePositiveReason(): String? =
        decorators.firstOrNull { it.name == "TaintRuleFalsePositive" }
            ?.arguments?.firstOrNull()

    private fun buildCp(sampleDir: Path): PIRClasspath {
        val samplePy = sampleDir.resolve("sample.py")
        require(samplePy.toFile().isFile) { "Missing sample.py under $sampleDir" }
        return PIRClasspathLoader(
            PIRSettings(
                sources = listOf(samplePy.absolutePathString()),
                mypyFlags = listOf(
                    "--ignore-missing-imports",
                    "--namespace-packages",
                    "--explicit-package-bases",
                ),
                rpcTimeout = java.time.Duration.ofSeconds(1200),
            )
        ).load()
    }

    private fun loadConfig(yamlFile: File): PIRTaintRulesProvider {
        val yaml = yamlFile.readText()
        val loader = SemgrepRuleLoader(listOf(PythonLanguageStrategy()))
        loader.registerRuleSet(yaml, Path(yamlFile.name), Path("."), SemgrepLoadTrace())
        val loadedRules = loader.loadRules()
        val rule = loadedRules.rulesWithMeta.firstOrNull()
            ?: fail("No rules loaded from $yamlFile")

        @Suppress("UNCHECKED_CAST")
        val typed = rule.first as TaintRuleFromSemgrep<SerializedPythonRule>
        val config: SerializedPythonTaintConfig = typed.toSerializedPythonTaintConfig()
        return PIRConfigTaintRulesProvider(PIRTaintConfiguration(config))
    }

    private fun runAnalysis(
        cp: PIRClasspath,
        config: PIRTaintRulesProvider,
        entryPoint: PIRFunction,
    ): List<TaintSinkTracker.TaintVulnerability> {
        val ifdsGraph = PIRApplicationGraph(cp)

        @Suppress("UNCHECKED_CAST")
        val engine = TaintAnalysisUnitRunnerManager(
            PIRAnalysisManager(cp, config),
            ifdsGraph as ApplicationGraph<CommonMethod, CommonInst>,
            unitResolver = { SingletonUnit },
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

    private fun PIRClass.allMethods(): List<PIRFunction> =
        methods + nestedClasses.flatMap { it.allMethods() }
}
