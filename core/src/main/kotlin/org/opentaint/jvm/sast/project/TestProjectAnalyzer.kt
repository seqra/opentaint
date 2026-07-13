package org.opentaint.jvm.sast.project

import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.decodeFromStream
import kotlinx.serialization.Serializable
import mu.KLogging
import org.opentaint.common.sast.ProjectAnalysisStatus
import org.opentaint.common.sast.rules.loadSemgrepRules
import org.opentaint.common.sast.sarif.DebugFactReachabilitySarifGenerator
import org.opentaint.common.sast.sarif.SarifGenerator
import org.opentaint.common.sast.test.ProjectAnalysisTestResults
import org.opentaint.common.sast.test.RuleInfo
import org.opentaint.common.sast.test.RuleSample
import org.opentaint.common.sast.test.RuleTest
import org.opentaint.common.sast.test.RuleTests
import org.opentaint.common.sast.test.SPRING_APP_SAMPLE_MODE
import org.opentaint.common.sast.test.TestProjectAnalyzerBase
import org.opentaint.common.sast.test.TestResult
import org.opentaint.common.sast.test.TestSampleInfo
import org.opentaint.common.sast.toProjectStatus
import org.opentaint.config.JavaDefaultConfigLoader
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.jvm.serialized.JavaConfigurationLoader
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedItem
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.sast.dataflow.JIRTaintAnalyzer
import org.opentaint.jvm.sast.project.TestProjectAnalyzer.JavaTestSampleInfo
import org.opentaint.jvm.sast.project.TestProjectAnalyzer.RuleSelectResult.Rule
import org.opentaint.jvm.sast.project.rules.analysisConfig
import org.opentaint.jvm.sast.project.rules.loadTaintConfig
import org.opentaint.jvm.sast.project.spring.springWebProjectEntryPoints
import org.opentaint.jvm.sast.sarif.JIRSarifTraits
import org.opentaint.jvm.sast.sarif.JirDebugFactReachabilitySarifGenerator
import org.opentaint.jvm.sast.sarif.JirSarifGenerator
import org.opentaint.jvm.sast.util.locationChecker
import org.opentaint.project.JavaProject
import org.opentaint.semgrep.pattern.RuleMetadata
import org.opentaint.semgrep.pattern.SemgrepRuleUtils
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import kotlin.io.path.exists
import kotlin.io.path.inputStream
import kotlin.reflect.KClass

class TestProjectAnalyzer(
    project: JavaProject,
    results: ProjectAnalysisTestResults,
    javaOptions: ProjectAnalysisOptions,
): TestProjectAnalyzerBase<JavaTestSampleInfo, ProjectAnalysisContext, JavaProject, JIRMethod, JIRInst, SerializedItem, SerializedTaintConfig>(
    project,
    results,
    javaOptions.common.copy(storeSummaries = false)
) {
    private val projectAnalysisContexts = initializeProjectModulesAnalysisContexts(project, javaOptions)
    private val loadedRules = options.loadSemgrepRules(JavaLanguageStrategy())

    @Serializable
    data class JavaTestSampleInfo(
        val className: String,
        val methodName: String?,
        val rule: RuleInfo,
        override val language: String,
        override val testSetName: String,
    ) : TestSampleInfo

    override fun testInfoCls(): KClass<JavaTestSampleInfo> = JavaTestSampleInfo::class
    override fun testInfoSerializer() = JavaTestSampleInfo.serializer()
    override fun defaultConfigLoader() = JavaDefaultConfigLoader
    override fun configLoader() = JavaConfigurationLoader()

    private var status: ProjectAnalysisStatus = ProjectAnalysisStatus.OK

    override fun analyze(): ProjectAnalysisStatus {
        val ruleTestsFile = project.sourceRoot?.resolve("rule-test.yaml")
        if (ruleTestsFile == null || !ruleTestsFile.exists()) {
            logger.error { "No test file in ${project.sourceRoot}" }
            return ProjectAnalysisStatus.EXCEPTION
        }

        val ruleTests = ruleTestsFile.inputStream().use {
            Yaml().decodeFromStream<RuleTests>(it)
        }

        val results = projectAnalysisContexts.map { (_, ctx) ->
            ctx.analyzeTestSamples(ruleTests.tests)
        }

        results.mapTo(this.results.testResults) {
            project to it
        }

        return status
    }

    private fun ProjectAnalysisContext.resolveSamples(
        rule: RuleInfo, kind: SampleKind, samples: List<RuleSample>, springEntryPoints: List<JIRMethod>
    ): List<TestSample> =
        samples.mapNotNull { sample ->
            val methods = if (sample.mode == SPRING_APP_SAMPLE_MODE) springEntryPoints else resolveMethods(sample.entrypoint)
            if (methods.isEmpty()) {
                logger.debug { "No sample found for ${sample.entrypoint} (mode=${sample.mode}) in this module" }
                return@mapNotNull null
            }
            val (className, methodName) = sample.entrypoint.splitIdentifier()
            TestSample(SampleInfo(kind, rule, sample.mode), className, methodName, methods)
        }

    private fun ProjectAnalysisContext.resolveMethods(id: String): List<JIRMethod> {
        val (className, methodName) = id.splitIdentifier()
        val normalized = className.replace('$', '.')
        val cls = projectClasses.allProjectClasses().firstOrNull { it.name.replace('$', '.') == normalized } ?: return emptyList()
        if (cls.isAbstract || cls.isInterface || cls.isAnonymous) return emptyList()
        return if (methodName == null) cls.declaredMethods else cls.declaredMethods.filter { it.name == methodName }
    }

    private fun ProjectAnalysisContext.analyzeTestSamples(tests: List<RuleTest>): TestResult<JavaTestSampleInfo> {
        val skipped = mutableListOf<RuleTest>()
        val disabled = mutableListOf<RuleTest>()

        logger.info { "Select test analysis rule" }

        val springEntryPoints = springWebProjectContext?.springWebProjectEntryPoints().orEmpty()

        val testWithRule = mutableListOf<Pair<TestSample, Rule>>()
        for (test in tests) {
            val ruleInfo = test.ruleId.toRuleInfo()
            val rules = when (val result = selectRules(ruleInfo)) {
                RuleSelectResult.MultipleRules,
                RuleSelectResult.NoRules -> {
                    skipped += test
                    continue
                }
                RuleSelectResult.RuleDisabled -> {
                    disabled += test
                    continue
                }
                is Rule -> result
            }

            val samples = resolveSamples(ruleInfo, SampleKind.POSITIVE, test.positive, springEntryPoints) +
                resolveSamples(ruleInfo, SampleKind.NEGATIVE, test.negative, springEntryPoints)
            samples.mapTo(testWithRule) { it to rules }
        }

        logger.info { "Start test analysis" }

        val results = mutableListOf<Triple<TestSample, Rule, AnalysisResult>>()
        for ((sample, rule) in testWithRule) {
            val analysisResult = analyzeTestSample(listOf(rule.rule), sample)

            status = maxOf(status, analysisResult.status.toProjectStatus())
            results += Triple(sample, rule, analysisResult)
        }

        for ((_, rule, result) in results) {
            generateReportFromAnalysisResult(result, listOf(rule.meta))
        }

        return generateTestResult(skipped, disabled, results)
    }

    private sealed interface RuleSelectResult {
        data class Rule(val rule: TaintRuleFromSemgrep<SerializedItem>, val meta: RuleMetadata): RuleSelectResult
        data object MultipleRules: RuleSelectResult
        data object NoRules: RuleSelectResult
        data object RuleDisabled: RuleSelectResult
    }

    private fun RuleInfo.ruleIdMatcher(): (String) -> Boolean {
        val ruleId = SemgrepRuleUtils.getRuleId(rulePath, ruleId ?: "")
        if (this.ruleId != null) {
            return { s: String -> s == ruleId }
        } else {
            return { s: String -> s.startsWith(ruleId) }
        }
    }

    private fun selectRules(info: RuleInfo): RuleSelectResult {
        val ruleIdMatcher = info.ruleIdMatcher()
        val relevantRules = loadedRules.rulesWithMeta.filter { ruleIdMatcher(it.first.ruleId) }

        return when (relevantRules.size) {
            1 -> {
                val rule = relevantRules.first()

                @Suppress("UNCHECKED_CAST")
                Rule(
                    rule.first as TaintRuleFromSemgrep<SerializedItem>,
                    rule.second
                )
            }

            0 -> {
                if (loadedRules.disabledRules.any { ruleIdMatcher(it) }){
                    logger.info { "Rule $info disabled" }
                    return RuleSelectResult.RuleDisabled
                }

                logger.error { "No rules found for $info" }
                RuleSelectResult.NoRules
            }

            else -> {
                logger.error { "Multiple rules found for $info" }
                RuleSelectResult.MultipleRules
            }
        }
    }

    private fun ProjectAnalysisContext.analyzeTestSample(
        rules: List<TaintRuleFromSemgrep<SerializedItem>>,
        sample: TestSample
    ): AnalysisResult {
        val loadedConfig = loadTaintConfig(cp, approximations.copy(rules = rules))
        val config = analysisConfig(loadedConfig)

        val analyzer = JIRTaintAnalyzer(
            cp, config,
            projectClasses = projectClasses.locationChecker(),
            options = options.taintAnalyzerOptions(),
        )

        return runAnalyzerWithTraceResolver(analyzer, sample.methods)
    }

    private fun generateTestResult(
        skipped: List<RuleTest>, disabled: List<RuleTest>,
        results: List<Triple<TestSample, Rule, AnalysisResult>>
    ): TestResult<JavaTestSampleInfo> {
        val success = mutableListOf<TestSample>()
        val falseNegative = mutableListOf<TestSample>()
        val falsePositive = mutableListOf<TestSample>()

        for ((test, _, testResult) in results) {
            when (test.info.kind) {
                SampleKind.POSITIVE -> if (testResult.traces.isEmpty()) {
                    falseNegative += test
                } else {
                    success += test
                }

                SampleKind.NEGATIVE -> if (testResult.traces.isNotEmpty()) {
                    falsePositive += test
                } else {
                    success += test
                }
            }
        }

        return TestResult(
            success = success.map(TestSample::toTestInfo),
            falseNegative = falseNegative.map(TestSample::toTestInfo),
            falsePositive = falsePositive.map(TestSample::toTestInfo),
            skipped = skipped.flatMap { it.toTestInfos() },
            disabled = disabled.flatMap { it.toTestInfos() },
        )
    }

    private enum class SampleKind {
        POSITIVE, NEGATIVE
    }

    private data class SampleInfo(val kind: SampleKind, val rule: RuleInfo, val testSet: String)

    private data class TestSample(
        val info: SampleInfo,
        val className: String,
        val methodName: String?,
        val methods: List<JIRMethod>,
    ) {
        fun toTestInfo(): JavaTestSampleInfo = JavaTestSampleInfo(
            className, methodName, info.rule, language = "java", info.testSet
        )
    }

    private fun RuleTest.toTestInfos(): List<JavaTestSampleInfo> {
        val rule = ruleId.toRuleInfo()
        return (positive + negative).map {
            val (className, methodName) = it.entrypoint.splitIdentifier()
            JavaTestSampleInfo(className, methodName, rule, language = "java", testSetName = it.mode)
        }
    }

    override fun ProjectAnalysisContext.runSeAnalyzer(
        engine: TaintAnalysisUnitRunnerManager,
        traces: List<VulnerabilityWithTrace>
    ): List<VulnerabilityWithTrace> {
        TODO("Not yet implemented")
    }

    override fun ProjectAnalysisContext.sarifGenerator(): SarifGenerator<*> {
        val sourcesResolver = project.sourceResolver(projectClasses)
        return JirSarifGenerator(
            options.sarifGenerationOptions, project.sourceRoot,
            sourcesResolver, JIRSarifTraits(cp)
        )
    }

    override fun ProjectAnalysisContext.debugSarifGenerator(): DebugFactReachabilitySarifGenerator<*> {
        val sourcesResolver = project.sourceResolver(projectClasses)
        return JirDebugFactReachabilitySarifGenerator(
            options.sarifGenerationOptions,
            sourcesResolver, JIRSarifTraits(cp)
        )
    }

    companion object {
        private val logger = object : KLogging() {}.logger

        private fun String.splitIdentifier(): Pair<String, String?> {
            val idx = indexOf('#')
            return if (idx < 0) this to null else substring(0, idx) to substring(idx + 1).ifEmpty { null }
        }

        private fun String.toRuleInfo(): RuleInfo {
            val idx = lastIndexOf('#')
            return if (idx < 0) RuleInfo(this, null)
            else RuleInfo(substring(0, idx), substring(idx + 1).ifEmpty { null })
        }
    }
}
