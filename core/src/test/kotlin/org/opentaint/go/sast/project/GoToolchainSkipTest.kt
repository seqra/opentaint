package org.opentaint.go.sast.project

import org.opentaint.common.sast.CommonAnalysisOptions
import org.opentaint.common.sast.CommonProjectAnalyzer
import org.opentaint.common.sast.ProjectAnalysisStatus
import org.opentaint.jvm.sast.project.ProjectAnalysisOptions
import org.opentaint.project.GoProject
import org.opentaint.project.Project
import java.nio.file.Files
import java.nio.file.Path
import kotlin.test.Test
import kotlin.test.assertEquals

class GoToolchainSkipTest {
    private val tmp: Path = Files.createTempDirectory("go-toolchain-skip-test")

    @Test
    fun `go project without go toolchain is skipped`() {
        assertEquals(ProjectAnalysisStatus.OK, analyze(GoProject(tmp.resolve("missing"))))
    }

    @Test
    fun `go project with a missing go toolchain is skipped`() {
        val project = GoProject(tmp.resolve("missing"), goToolchain = tmp.resolve("no-goroot"))
        assertEquals(ProjectAnalysisStatus.OK, analyze(project))
    }

    private fun analyze(project: GoProject): ProjectAnalysisStatus {
        val options = object : CommonProjectAnalyzer.OptionProvider {
            override fun commonOptions() = CommonAnalysisOptions()
            override fun javaOptions(): ProjectAnalysisOptions = error("No Java project")
            override fun goOptions() = GoProjectAnalysisOptions()
        }
        return CommonProjectAnalyzer(Project(goProjects = listOf(project)), tmp, runInTestMode = false, options).run()
    }
}
