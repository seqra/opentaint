package org.opentaint.jvm.sast.project

import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import ch.qos.logback.classic.spi.ILoggingEvent
import ch.qos.logback.core.read.ListAppender
import org.junit.jupiter.api.io.TempDir
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource
import org.opentaint.common.sast.CommonAnalysisOptions
import org.opentaint.common.sast.ProjectAnalysisStatus
import org.opentaint.common.sast.test.ProjectAnalysisTestResults
import org.opentaint.dataflow.bidi.driver.IterationDriver
import org.opentaint.project.JavaProject
import org.opentaint.project.ProjectModuleClasses
import org.slf4j.LoggerFactory
import java.io.File
import java.nio.file.Path
import kotlin.io.path.createDirectories
import kotlin.io.path.writeText
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.seconds

class RuleTestEngineSelectionTest {
    @TempDir
    lateinit var directory: Path

    @ParameterizedTest
    @ValueSource(booleans = [false, true])
    fun `rule runner selects the requested engine and evaluates the source sink sample`(bidirectional: Boolean) {
        val rule = directory.resolve("rules").createDirectories().resolve("runner.yaml").apply {
            writeText("""
                rules:
                  - id: runner-engine-selection
                    message: Runner source reaches sink
                    severity: WARNING
                    languages: [java]
                    mode: taint
                    pattern-sources:
                      - pattern: ${'$'}S.source()
                    pattern-sinks:
                      - pattern: ${'$'}S.sink(${'$'}X)
            """.trimIndent())
        }
        directory.resolve("rule-test.yaml").writeText("""
            tests:
              - rule-id: runner.yaml#runner-engine-selection
                positive:
                  - test.samples.SimpleDataFlowSample#simpleDataFlow
        """.trimIndent())
        val samples = Path.of(checkNotNull(System.getenv("TEST_SAMPLES_JAR")))
        val dependencies = checkNotNull(System.getenv("TEST_DEPENDENCIES_JAR"))
            .split(File.pathSeparator).filter(String::isNotEmpty).map(Path::of)
        val project = JavaProject(
            sourceRoot = directory,
            modules = listOf(ProjectModuleClasses(moduleSourceRoot = directory, moduleClasses = listOf(samples))),
            dependencies = dependencies,
        )
        val options = CommonAnalysisOptions(
            semgrepRuleSet = listOf(rule.parent),
            ifdsAnalysisTimeout = 20.seconds,
            ifdsBidirectional = bidirectional,
        )
        val results = ProjectAnalysisTestResults(directory.resolve("result").createDirectories(), options)
        val logger = LoggerFactory.getLogger(IterationDriver::class.java) as Logger
        val previousLevel = logger.level
        val events = ListAppender<ILoggingEvent>().apply { start() }
        logger.level = Level.INFO
        logger.addAppender(events)
        try {
            val runner = TestProjectAnalyzer(project, results, ProjectAnalysisOptions(common = options))
            assertEquals(ProjectAnalysisStatus.OK, runner.analyze())
            val result = results.testResults.single().second
            assertEquals(1, result.success.size, result.toString())
            assertTrue(result.falseNegative.isEmpty())
            assertTrue(result.falsePositive.isEmpty())
            assertTrue(result.skipped.isEmpty())
            assertTrue(result.disabled.isEmpty())
            val runs = events.list.filter { it.formattedMessage.startsWith("BIDI_RUN_START ") }
            assertEquals(bidirectional, runs.isNotEmpty(), "The actual runner must enter the selected engine")
            if (bidirectional) {
                assertTrue(runs.first().formattedMessage.contains("run=1 direction=FORWARD limit=1"))
                assertTrue(events.list.any { it.formattedMessage.startsWith("BIDI_ANALYSIS_END ") })
            }
        } finally {
            logger.detachAppender(events)
            logger.level = previousLevel
            events.stop()
        }
    }
}
