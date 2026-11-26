package org.opentaint.project

import java.nio.file.Files
import kotlin.io.path.Path
import kotlin.io.path.readText
import kotlin.test.Test
import kotlin.test.assertEquals

class BuildStatusTest {
    private val dir = Files.createTempDirectory("build-status-test").resolve("model")

    private fun BuildStatus.written(): String {
        write(dir)
        return dir.resolve(BuildStatus.FILE_NAME).readText()
    }

    @Test
    fun `no projects`() {
        assertEquals(
            """
            {
                "projects": []
            }
            """.trimIndent(),
            BuildStatus(emptyList()).written(),
        )
    }

    @Test
    fun `built and failed projects`() {
        val status = BuildStatus(
            listOf(
                ProjectStatus.Failed(
                    Language.JAVA,
                    Path("/home/u/app/java"),
                    listOf(
                        BuildError(Path("/usr/lib/jvm/temurin-17"), listOf("Execution failed for task ':compileJava'.")),
                        BuildError(toolchain = null, causes = listOf("Could not find Maven executable")),
                    ),
                ),
                ProjectStatus.Built(Language.JAVA, Path("/home/u/app/cp"), toolchain = null),
                ProjectStatus.Built(Language.GO, Path("/home/u/app/svc"), Path("/usr/local/go")),
            )
        )

        assertEquals(
            """
            {
                "projects": [
                    {
                        "language": "java",
                        "project": "/home/u/app/java",
                        "errors": [
                            {
                                "toolchain": "/usr/lib/jvm/temurin-17",
                                "causes": [
                                    "Execution failed for task ':compileJava'."
                                ]
                            },
                            {
                                "toolchain": null,
                                "causes": [
                                    "Could not find Maven executable"
                                ]
                            }
                        ]
                    },
                    {
                        "language": "java",
                        "project": "/home/u/app/cp",
                        "toolchain": null
                    },
                    {
                        "language": "go",
                        "project": "/home/u/app/svc",
                        "toolchain": "/usr/local/go"
                    }
                ]
            }
            """.trimIndent(),
            status.written(),
        )
    }
}
