package org.opentaint.project

import kotlin.test.Test
import kotlin.test.assertEquals

class BuildFailureCausesTest {
    private fun BuildFailureCauses.parse(lines: List<String>, exitCode: Int = 1): List<String> {
        lines.forEach(::accept)
        return causes(exitCode)
    }

    private fun sample(name: String): List<String> =
        javaClass.getResource("/build-output/$name")!!.readText().lines()

    @Test
    fun `gradle compilation failure`() {
        assertEquals(
            listOf(
                "Execution failed for task ':compileJava'.",
                "Compilation failed; see the compiler output below.",
                "/home/u/app/src/main/java/app/App.java:13: error: illegal start of expression",
                "class Broken { int x = ; }",
                "^",
                "1 error",
            ),
            GradleFailureCauses().parse(sample("gradle-compile.txt")),
        )
    }

    @Test
    fun `gradle run with a JRE`() {
        assertEquals(
            listOf(
                "Could not determine the dependencies of task ':compileJava'.",
                "Could not resolve all dependencies for configuration ':compileClasspath'.",
                "Failed to calculate the value of task ':compileJava' property 'javaCompiler'.",
                "Toolchain installation '/home/u/.opentaint/install/jre' does not provide the required capabilities: [JAVA_COMPILER]",
            ),
            GradleFailureCauses().parse(sample("gradle-jre.txt")),
        )
    }

    @Test
    fun `gradle failures of several tasks`() {
        val output = """
            FAILURE: Build completed with 2 failures.

            1: Task failed with an exception.
            -----------
            * What went wrong:
            Execution failed for task ':a:compileJava'.

            * Try:
            > Run with --info or --debug option to get more log output.
            ==============================================================================

            2: Task failed with an exception.
            -----------
            * What went wrong:
            Execution failed for task ':b:compileJava'.
            > Compilation failed; see the compiler output below.

            * Try:
            > Run with --info or --debug option to get more log output.
        """.trimIndent().lines()

        assertEquals(
            listOf(
                "Execution failed for task ':a:compileJava'.",
                "Execution failed for task ':b:compileJava'.",
                "Compilation failed; see the compiler output below.",
            ),
            GradleFailureCauses().parse(output),
        )
    }

    @Test
    fun `maven compilation failure`() {
        assertEquals(
            listOf(
                "Failed to execute goal org.apache.maven.plugins:maven-compiler-plugin:3.1:compile (default-compile) on project app: Compilation failure: Compilation failure:",
                "Source option 5 is no longer supported. Use 8 or later.",
                "Target option 5 is no longer supported. Use 8 or later.",
            ),
            MavenFailureCauses().parse(sample("maven-compile.txt")),
        )
    }

    @Test
    fun `maven one-line failure`() {
        val output = listOf(
            "[ERROR] Failed to execute goal org.apache.maven.plugins:maven-compiler-plugin:3.1:compile (default-compile) on project app: No compiler is provided in this environment. Perhaps you are running on a JRE rather than a JDK? -> [Help 1]",
            "[ERROR] ",
            "[ERROR] [Help 1] http://cwiki.apache.org/confluence/display/MAVEN/MojoFailureException",
        )

        assertEquals(
            listOf(
                "Failed to execute goal org.apache.maven.plugins:maven-compiler-plugin:3.1:compile (default-compile) on project app: No compiler is provided in this environment. Perhaps you are running on a JRE rather than a JDK?",
            ),
            MavenFailureCauses().parse(output),
        )
    }

    @Test
    fun `exit code without a failure block`() {
        val output = listOf("Error: JAVA_HOME is not defined correctly.")

        assertEquals(listOf("the Gradle build failed with exit code 1"), GradleFailureCauses().parse(output))
        assertEquals(listOf("the Maven build failed with exit code 127"), MavenFailureCauses().parse(output, 127))
    }
}
