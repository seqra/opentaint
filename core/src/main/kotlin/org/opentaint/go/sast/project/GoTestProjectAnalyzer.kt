package org.opentaint.go.sast.project

import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.decodeFromStream
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.encodeToStream
import mu.KLogging
import org.opentaint.common.sast.ProjectAnalysisStatus
import org.opentaint.common.sast.ProjectAnalyzer
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.rules.loadSemgrepRules
import org.opentaint.common.sast.toProjectStatus
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.go.sast.dataflow.GoTaintAnalyzer
import org.opentaint.go.sast.dataflow.GoUnitResolver
import org.opentaint.go.sast.sarif.GoSarifGenerator
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.util.io.inputStream
import org.opentaint.project.GoProject
import org.opentaint.semgrep.go.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import java.nio.file.Path
import kotlin.io.path.div
import kotlin.io.path.exists
import kotlin.io.path.outputStream

class GoTestProjectAnalyzer(
    val project: GoProject,
    private val resultDir: Path,
    providedOptions: GoProjectAnalysisOptions,
) {
    private val options = with(providedOptions) { copy(common = common.copy(storeSummaries = false)) }
    private val loadedRules = options.common.loadSemgrepRules(GoLanguageStrategy())


    @Serializable
    data class RuleTests(
        val tests: List<RuleTest>,
    )

    @Serializable
    data class RuleTest(
        @SerialName("rule-id")
        val ruleId: String,
        val positive: List<String> = emptyList(),
        val negative: List<String> = emptyList(),
    )

    @Serializable
    data class TestResult(
        val success: List<RuleTest>,
        val falseNegative: List<RuleTest>,
        val falsePositive: List<RuleTest>,
        val skipped: List<RuleTest>,
        val disabled: List<RuleTest>,
    )

    private data class RuleTestSample(
        val ruleId: String,
        val kind: SampleKind,
        val entryPoint: GoIRFunction,
    )

    private var status: ProjectAnalysisStatus = ProjectAnalysisStatus.OK

    fun analyze(): ProjectAnalysisStatus {
        val ruleTestsFile = project.projectDir.resolve("rule-test.yaml")
        if (!ruleTestsFile.exists()) {
            logger.error("No test file in ${project.projectDir}")
            return ProjectAnalysisStatus.EXCEPTION
        }

        val ruleTests = ruleTestsFile.inputStream().use {
            Yaml().decodeFromStream<RuleTests>(it)
        }

        val ctx = AnalysisCtx(project, GoIRClient())

        val results = ctx.analyzeTestSamples(ruleTests.tests)
            ?: return ProjectAnalysisStatus.EXCEPTION

        writeTestResult(results)

        return status
    }

    private fun AnalysisCtx.analyzeTestSamples(tests: List<RuleTest>): TestResult? {
        val skipped = mutableListOf<RuleTest>()
        val disabled = mutableListOf<RuleTest>()

        logger.info { "Select test analysis rules" }

        val testWithRule = mutableListOf<Pair<RuleTestSample, List<TaintRuleFromSemgrep<GoSerializedItem>>>>()
        val testGroups = tests.groupBy { it.ruleId }
        for ((ruleInfo, testGroup) in testGroups) {
            val rules = when (val result = selectRules(ruleInfo)) {
                RuleSelectResult.MultipleRules, RuleSelectResult.NoRules -> {
                    skipped += testGroup
                    continue
                }

                RuleSelectResult.RuleDisabled -> {
                    disabled += testGroup
                    continue
                }

                is RuleSelectResult.Rules -> result.rules
            }

            val samples = mutableListOf<RuleTestSample>()
            testGroup.forEach { group ->
                group.positive.mapTo(samples) {
                    val ep = resolveEntryPoint(it) ?: return null
                    RuleTestSample(ruleInfo, SampleKind.POSITIVE, ep)
                }
                group.negative.mapTo(samples) {
                    val ep = resolveEntryPoint(it) ?: return null
                    RuleTestSample(ruleInfo, SampleKind.NEGATIVE, ep)
                }
            }

            samples.mapTo(testWithRule) { it to rules }
        }

        logger.info { "Start test analysis" }

        val results = mutableListOf<Pair<RuleTestSample, List<VulnerabilityWithTrace>>>()
        for ((sample, rules) in testWithRule) {
            val (analysisResult, analysisStatus) = analyzeTestSample(rules, sample)

            status = maxOf(status, analysisStatus.toProjectStatus())
            results += sample to analysisResult
        }

        generateSarif(results.flatMap { it.second })

        return generateTestResult(skipped, disabled, results)
    }

    private fun AnalysisCtx.resolveEntryPoint(name: String): GoIRFunction? =
        cp.allFunctions().firstOrNull { it.fullName == name }

    private sealed interface RuleSelectResult {
        data class Rules(val rules: List<TaintRuleFromSemgrep<GoSerializedItem>>) : RuleSelectResult
        data object MultipleRules : RuleSelectResult
        data object NoRules : RuleSelectResult
        data object RuleDisabled : RuleSelectResult
    }

    private fun selectRules(testRuleId: String): RuleSelectResult {
        val loadedRuleId = testRuleId.replace('#', ':')

        val relevantRules = loadedRules.rulesWithMeta.filter { it.first.ruleId == loadedRuleId }
        return when (relevantRules.size) {
            1 -> {
                @Suppress("UNCHECKED_CAST") RuleSelectResult.Rules(relevantRules.map { it.first as TaintRuleFromSemgrep<GoSerializedItem> })
            }

            0 -> {
                if (loadedRules.disabledRules.any { it == loadedRuleId }) {
                    logger.info { "Rule $testRuleId disabled" }
                    return RuleSelectResult.RuleDisabled
                }

                logger.error { "No rules found for $testRuleId" }
                RuleSelectResult.NoRules
            }

            else -> {
                logger.error { "Multiple rules found for $testRuleId" }
                RuleSelectResult.MultipleRules
            }
        }
    }

    private fun AnalysisCtx.analyzeTestSample(
        rules: List<TaintRuleFromSemgrep<GoSerializedItem>>, sample: RuleTestSample
    ): Pair<List<VulnerabilityWithTrace>, TaintAnalyzer.Status> {
        val rulesProvider = ProjectAnalyzer.PreloadedRules(
            rules,
            customApproximationConfig = emptyList<GoSerializedTaintConfig>()
        ).loadRules()

        GoTaintAnalyzer(
            cp,
            rulesProvider,
            GoUnitResolver(),
            options.common.taintAnalyzerOptions(),
        ).use { analyzer ->
            logger.info { "Start IFDS analysis for test: $sample" }
            val traces = analyzer.analyzeWithIfds(listOf(sample.entryPoint))
            logger.info { "Finish IFDS analysis for test: $sample" }
            return traces
        }
    }

    private enum class SampleKind {
        POSITIVE, NEGATIVE
    }

    private fun generateTestResult(
        skipped: List<RuleTest>, disabled: List<RuleTest>,
        results: List<Pair<RuleTestSample, List<VulnerabilityWithTrace>>>
    ): TestResult {
        val success = mutableListOf<RuleTestSample>()
        val falseNegative = mutableListOf<RuleTestSample>()
        val falsePositive = mutableListOf<RuleTestSample>()

        for ((test, testResult) in results) {
            when (test.kind) {
                SampleKind.POSITIVE -> if (testResult.isEmpty()) {
                    falseNegative += test
                } else {
                    success += test
                }

                SampleKind.NEGATIVE -> if (testResult.isNotEmpty()) {
                    falsePositive += test
                } else {
                    success += test
                }
            }
        }

        return TestResult(
            success = success.toRuleTest(),
            falseNegative = falseNegative.toRuleTest(),
            falsePositive = falsePositive.toRuleTest(),
            skipped = skipped,
            disabled = disabled,
        )
    }

    private fun List<RuleTestSample>.toRuleTest() =
        groupBy { it.ruleId }.mapValues { (ruleId, tests) -> tests.toRuleTest(ruleId) }.values.toList()

    private fun List<RuleTestSample>.toRuleTest(ruleId: String): RuleTest {
        val positive = mutableListOf<String>()
        val negative = mutableListOf<String>()
        forEach { sample ->
            val name = sample.entryPoint.fullName
            val collection = when (sample.kind) {
                SampleKind.POSITIVE -> positive
                SampleKind.NEGATIVE -> negative
            }
            collection += name
        }
        return RuleTest(ruleId, positive, negative)
    }

    private fun generateSarif(traces: List<VulnerabilityWithTrace>) {
        val generator = GoSarifGenerator(options.common.sarifGenerationOptions, project.sourceRoot())
        (resultDir / options.common.sarifGenerationOptions.sarifFileName).outputStream().use { out ->
            generator.generateSarif(out, traces.asSequence(), loadedRules.rulesWithMeta.map { it.second })
        }
    }

    @OptIn(ExperimentalSerializationApi::class)
    private fun writeTestResult(testResult: TestResult) {
        val json = Json { prettyPrint = true }
        (resultDir / "test-result.json").outputStream().use { out ->
            json.encodeToStream(testResult, out)
        }
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}
