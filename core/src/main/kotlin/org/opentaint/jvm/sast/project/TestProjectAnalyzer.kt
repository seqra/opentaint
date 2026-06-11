package org.opentaint.jvm.sast.project

import kotlinx.serialization.Serializable
import mu.KLogging
import org.opentaint.common.sast.ProjectAnalysisStatus
import org.opentaint.common.sast.rules.loadSemgrepRules
import org.opentaint.common.sast.sarif.DebugFactReachabilitySarifGenerator
import org.opentaint.common.sast.sarif.SarifGenerator
import org.opentaint.common.sast.test.ProjectAnalysisTestResults
import org.opentaint.common.sast.test.RuleInfo
import org.opentaint.common.sast.test.TestProjectAnalyzerBase
import org.opentaint.common.sast.test.TestResult
import org.opentaint.common.sast.test.TestSampleInfo
import org.opentaint.common.sast.toProjectStatus
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedItem
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.loadSerializedTaintConfig
import org.opentaint.ir.api.jvm.JIRAnnotated
import org.opentaint.ir.api.jvm.JIRAnnotation
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.sast.dataflow.JIRTaintAnalyzer
import org.opentaint.jvm.sast.project.TestProjectAnalyzer.JavaTestSampleInfo
import org.opentaint.jvm.sast.project.TestProjectAnalyzer.RuleSelectResult.Rule
import org.opentaint.jvm.sast.project.rules.analysisConfig
import org.opentaint.jvm.sast.project.rules.semgrepRulesWithDefaultConfig
import org.opentaint.jvm.sast.project.rules.withApproximationConfigs
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
import kotlin.io.path.inputStream
import kotlin.io.path.relativeTo
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

    private val approximationConfigs: List<SerializedTaintConfig> =
        options.customApproximationConfig.map { cfg ->
            cfg.inputStream().use { loadSerializedTaintConfig(it) }
        }

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

    private var status: ProjectAnalysisStatus = ProjectAnalysisStatus.OK

    override fun analyze(): ProjectAnalysisStatus {
        val results = projectAnalysisContexts.map { (module, ctx) ->
            val testSetName = ctx.project.sourceRoot?.let { srcRoot ->
                module.moduleSourceRoot?.relativeTo(srcRoot)?.toString()
            }.orEmpty().replace('/', '-')

            val testSamples = ctx.allProjectTestSamples(testSetName)
            ctx.analyzeTestSamples(testSamples)
        }

        results.mapTo(this.results.testResults) {
            project to it
        }

        return status
    }

    private fun ProjectAnalysisContext.allProjectTestSamples(testSetName: String): List<TestSample> {
        val samples = mutableListOf<TestSample>()

        val classes = projectClasses.allProjectClasses()
            .filterNotTo(mutableListOf()) { it.isAbstract || it.isInterface || it.isAnonymous }

        classes.mapNotNullTo(samples) { cls ->
            val sample = cls.findSampleAnnotation(testSetName) ?: return@mapNotNullTo null
            ClassTestSample(cls, cls.declaredMethods, sample)
        }

        classes.flatMapTo(mutableListOf()) { it.declaredMethods }
            .mapNotNullTo(samples) {
                val sample = it.findSampleAnnotation(testSetName) ?: return@mapNotNullTo null
                MethodTestSample(it, sample)
            }

        if (!testSetName.isSpringAppTestSet()) return samples

        logger.info { "Detect spring test set: $testSetName" }

        val springEp = springWebProjectContext?.springWebProjectEntryPoints()?.takeIf { it.isNotEmpty() }
        if (springEp == null) {
            logger.error { "No spring entry point found: $testSetName" }
            return samples
        }

        return samples.map { SpringTestSample(springEp, it) }
    }

    private fun ProjectAnalysisContext.analyzeTestSamples(testSamples: List<TestSample>): TestResult<JavaTestSampleInfo> {
        val skipped = mutableListOf<TestSample>()
        val disabled = mutableListOf<TestSample>()

        logger.info { "Select test analysis rule" }

        val testWithRule = mutableListOf<Pair<TestSample, Rule>>()
        val testGroups = testSamples.groupBy { it.info.rule }
        for ((ruleInfo, testGroup) in testGroups) {
            val rules = when (val result = selectRules(ruleInfo)) {
                RuleSelectResult.MultipleRules,
                RuleSelectResult.NoRules -> {
                    skipped += testGroup
                    continue
                }
                RuleSelectResult.RuleDisabled -> {
                    disabled += testGroup
                    continue
                }
                is Rule -> result
            }

            testGroup.mapTo(testWithRule) { it to rules }
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
        val loadedConfig = rules.semgrepRulesWithDefaultConfig(cp)
            .withApproximationConfigs(cp, approximationConfigs)
        val config = analysisConfig(loadedConfig)

        val analyzer = JIRTaintAnalyzer(
            cp, config,
            projectClasses = projectClasses.locationChecker(),
            options = options.taintAnalyzerOptions(),
        )

        return runAnalyzerWithTraceResolver(analyzer, sample.methods)
    }

    private fun generateTestResult(
        skipped: List<TestSample>, disabled: List<TestSample>,
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
            skipped = skipped.map(TestSample::toTestInfo),
            disabled = disabled.map(TestSample::toTestInfo),
        )
    }

    private enum class SampleKind {
        POSITIVE, NEGATIVE
    }

    private data class SampleInfo(val kind: SampleKind, val rule: RuleInfo, val testSet: String)

    private sealed interface TestSample {
        val info: SampleInfo
        val methods: List<JIRMethod>

        fun toTestInfo(): JavaTestSampleInfo
    }

    private data class MethodTestSample(val method: JIRMethod, override val info: SampleInfo) : TestSample {
        override val methods: List<JIRMethod> get() = listOf(method)

        override fun toTestInfo(): JavaTestSampleInfo = JavaTestSampleInfo(
            method.enclosingClass.name, method.name, info.rule, language = "java", info.testSet
        )
    }

    private data class ClassTestSample(
        val cls: JIRClassOrInterface,
        override val methods: List<JIRMethod>,
        override val info: SampleInfo
    ) : TestSample {
        override fun toTestInfo(): JavaTestSampleInfo = JavaTestSampleInfo(
            cls.name, methodName = null, info.rule, language = "java", info.testSet
        )
    }

    private data class SpringTestSample(
        override val methods: List<JIRMethod>,
        val original: TestSample,
    ) : TestSample {
        override val info: SampleInfo get() = original.info
        override fun toTestInfo(): JavaTestSampleInfo = original.toTestInfo()
    }

    private fun JIRAnnotated.findSampleAnnotation(testSetName: String): SampleInfo? {
        val positive = annotations.filter { it.name == POSITIVE_SAMPLE_ANNOTATION_NAME }
        val negative = annotations.filter { it.name == NEGATIVE_SAMPLE_ANNOTATION_NAME }
        val sampleAnnotations = positive + negative
        if (sampleAnnotations.isEmpty()) return null
        if (sampleAnnotations.size > 1) {
            logger.error { "Multiple sample annotations: $this" }
            return null
        }
        return sampleAnnotations.first().toSampleInfo(testSetName)
    }

    private fun JIRAnnotation.toSampleInfo(testSetName: String): SampleInfo? {
        val kind = when (name) {
            POSITIVE_SAMPLE_ANNOTATION_NAME -> SampleKind.POSITIVE
            NEGATIVE_SAMPLE_ANNOTATION_NAME -> SampleKind.NEGATIVE
            else -> return null
        }

        val rulePath = values["value"]?.let { it as? String }?.takeIf { it.isNotBlank() }
        val ruleId = values["id"]?.let { it as? String }?.takeIf { it.isNotBlank() }

        if (rulePath == null) {
            logger.error { "Annotation without rule path: $this" }
            return null
        }

        return SampleInfo(kind, RuleInfo(rulePath, ruleId), testSetName)
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

        private const val POSITIVE_SAMPLE_ANNOTATION_NAME = "org.opentaint.sast.test.util.PositiveRuleSample"
        private const val NEGATIVE_SAMPLE_ANNOTATION_NAME = "org.opentaint.sast.test.util.NegativeRuleSample"

        private fun String.isSpringAppTestSet(): Boolean = startsWith("spring-app-tests")
    }
}
