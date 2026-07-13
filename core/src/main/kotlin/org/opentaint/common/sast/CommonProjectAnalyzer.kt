package org.opentaint.common.sast

import mu.KLogging
import org.opentaint.common.sast.test.ProjectAnalysisTestResults
import org.opentaint.common.sast.test.TestProjectAnalyzerBase
import org.opentaint.common.sast.test.TestSampleInfo
import org.opentaint.go.sast.project.GoProjectAnalysisOptions
import org.opentaint.go.sast.project.GoProjectAnalyzer
import org.opentaint.go.sast.project.GoTestProjectAnalyzer
import org.opentaint.jvm.sast.project.JirProjectAnalyzer
import org.opentaint.jvm.sast.project.ProjectAnalysisOptions
import org.opentaint.jvm.sast.project.TestProjectAnalyzer
import org.opentaint.project.CommonProject
import org.opentaint.project.GoProject
import org.opentaint.project.JavaProject
import org.opentaint.project.Project
import java.nio.file.Path

class CommonProjectAnalyzer(
    val project: Project,
    val outputDir: Path,
    val runInTestMode: Boolean,
    val options: OptionProvider
) {
    interface OptionProvider {
        fun commonOptions(): CommonAnalysisOptions
        fun javaOptions(): ProjectAnalysisOptions
        fun goOptions(): GoProjectAnalysisOptions
    }

    val allProjects = project.javaProjects + project.goProjects

    fun run(): ProjectAnalysisStatus = if (!runInTestMode) {
        runAnalysis()
    } else {
        runTests()
    }

    private fun runAnalysis() = runAnyAnalyzer(
        { ProjectAnalysisResults(outputDir, options.commonOptions()) },
        { project, results ->
            val analyzer = when (project) {
                is JavaProject -> javaProjectAnalyzer(project, results)
                is GoProject -> goProjectAnalyzer(project, results)
            }
            analyzer.analyze()
        }
    )

    private fun runTests(): ProjectAnalysisStatus = runAnyAnalyzer(
        { ProjectAnalysisTestResults(outputDir, options.commonOptions()) },
        { project, results ->
            val analyzer = when (project) {
                is JavaProject -> javaProjectTestAnalyzer(project, results)
                is GoProject -> goProjectTestAnalyzer(project, results)
            }
            results.registerAnalyzer(analyzer)
            analyzer.analyze()
        }
    )

    private fun <T : TestSampleInfo> ProjectAnalysisTestResults.registerAnalyzer(
        analyzer: TestProjectAnalyzerBase<T, *, *, *, *, *, *>
    ) {
        registerTestInfo(analyzer.testInfoCls(), analyzer.testInfoSerializer())
    }

    private inline fun <R : ProjectAnalysisResults> runAnyAnalyzer(
        mkResults: () -> R,
        createAndRunAnalyzer: (CommonProject, R) -> ProjectAnalysisStatus,
    ): ProjectAnalysisStatus {
        val results = mkResults()

        var status = ProjectAnalysisStatus.OK
        for (project in allProjects) {
            val projectName = project.projectName()
            val projectStatus = try {
                logger.info { "Start analysis for project: $projectName" }
                createAndRunAnalyzer(project, results).also {
                    logger.info { "Finish analysis for project: $projectName" }
                }
            } catch (ex: Throwable) {
                logger.error(ex) { "Fail analysis for project: $projectName" }
                ProjectAnalysisStatus.EXCEPTION
            }

            status = maxOf(status, projectStatus)
        }

        results.writeResults()

        return status
    }

    private fun javaProjectAnalyzer(project: JavaProject, results: ProjectAnalysisResults) =
        JirProjectAnalyzer(project, results, options.javaOptions())

    private fun goProjectAnalyzer(project: GoProject, results: ProjectAnalysisResults) =
        GoProjectAnalyzer(project, results, options.goOptions())

    private fun javaProjectTestAnalyzer(project: JavaProject, results: ProjectAnalysisTestResults) =
        TestProjectAnalyzer(project, results, options.javaOptions())

    private fun goProjectTestAnalyzer(project: GoProject, results: ProjectAnalysisTestResults) =
        GoTestProjectAnalyzer(project, results, options.goOptions())

    private fun CommonProject.projectName(): String = when (this) {
        is JavaProject -> sourceRoot.toString()
        is GoProject -> projectDir.toString()
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}
