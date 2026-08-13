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
 * Runs the real autobuilder Gradle pipeline against a small project with a versioned Maven Central
 * dependency and checks the emitted model. Shells out to Gradle and needs network access (Maven
 * Central + the Gradle Plugin Portal).
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

            // Re-parse from the emitted YAML, like a real consumer would.
            val loaded = JavaProject.load(modelPath)

            assertTrue(loaded.dependencies.isNotEmpty(), "Expected at least one resolved dependency")

            // Invariant 1: every dependency is tagged with a purl, not a bare path.
            loaded.dependencies.forEach { dep ->
                assertNotNull(dep.purl, "Untagged dependency (missing purl): $dep")
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

            // Invariant 4: the resolved version reflects what the build declares, not a stray cached one.
            val commonsLang3 = loaded.dependencies.singleOrNull {
                it.purl == "pkg:maven/org.apache.commons/commons-lang3@3.14.0"
            } ?: fail("Expected a resolved commons-lang3 dependency, got: ${loaded.dependencies}")
            assertEquals("pkg:maven/org.apache.commons/commons-lang3@3.14.0", commonsLang3.purl)
        } finally {
            workRoot.deleteRecursively()
        }
    }
}
