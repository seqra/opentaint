package org.opentaint.project

import java.nio.file.Files
import kotlin.io.path.createDirectories
import kotlin.io.path.deleteRecursively
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.exists
import kotlin.io.path.isRegularFile
import kotlin.io.path.pathString
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * End-to-end acceptance for reliable tagged dependency resolution: runs the real autobuilder
 * Gradle pipeline (init-script dependency graph + resolution table) against a small Gradle
 * project with a real, versioned, external Maven Central dependency, then checks the emitted
 * project model.
 *
 * This is a genuine integration test: it shells out to a real Gradle build and needs network
 * access to Maven Central (for the fixture's `commons-lang3` dependency) and the Gradle Plugin
 * Portal (for the `github-dependency-graph-gradle-plugin` init script). See
 * `.superpowers/sdd/task-6-report.md` for the manual acceptance run this mirrors, and for the
 * evidence captured against the full real-world repro-kit project.
 */
@OptIn(ExperimentalPathApi::class)
class GradleTaggedResolutionIT {
    @Test
    fun `gradle project dependencies come out tagged with coordinates and resolved to real files`() {
        val fixtureResource = javaClass.classLoader.getResource("gradle-fixture-project")
            ?: fail("gradle-fixture-project test resource not found on classpath")

        val workRoot = Files.createTempDirectory("gradle-tagged-resolution-it")
        try {
            val projectDir = workRoot.resolve("project").createDirectories()
            java.nio.file.Paths.get(fixtureResource.toURI()).copyDirRecursivelyTo(projectDir)

            val buildDir = workRoot.resolve("build").createDirectories()
            val resolved = ProjectResolver.resolveProject(projectDir, buildDir)
                ?: fail("Autobuilder failed to resolve the fixture Gradle project")

            val modelPath = workRoot.resolve("model.yaml")
            resolved.dump(modelPath)

            // Re-parse from the emitted YAML, exactly like a real consumer of the autobuilder's
            // output would.
            val loaded = JavaProject.load(modelPath)

            assertTrue(loaded.dependencies.isNotEmpty(), "Expected at least one resolved dependency")

            // Invariant 1: every dependency is tagged with group/artifact/version, not a bare path.
            loaded.dependencies.forEach { dep ->
                assertNotNull(dep.group, "Untagged dependency (missing group): $dep")
                assertNotNull(dep.artifact, "Untagged dependency (missing artifact): $dep")
                assertNotNull(dep.version, "Untagged dependency (missing version): $dep")
            }

            // Invariant 2: every dependency path resolves to a real file on disk.
            loaded.dependencies.forEach { dep ->
                assertTrue(
                    dep.path.exists() && dep.path.isRegularFile(),
                    "Dependency path does not exist on disk: ${dep.path}"
                )
            }

            // Invariant 3: no dependency path leaks a project/module build output directory.
            loaded.dependencies.forEach { dep ->
                assertFalse(
                    dep.path.pathString.contains("build/classes"),
                    "Dependency path leaks a project class directory: ${dep.path}"
                )
            }

            // Invariant 4: the resolved version reflects what the build actually declares/resolves,
            // not a stray cached version.
            val commonsLang3 = loaded.dependencies.singleOrNull { it.artifact == "commons-lang3" }
                ?: fail("Expected a resolved commons-lang3 dependency, got: ${loaded.dependencies}")
            assertEquals("org.apache.commons", commonsLang3.group)
            assertEquals("3.14.0", commonsLang3.version)
        } finally {
            workRoot.deleteRecursively()
        }
    }
}
