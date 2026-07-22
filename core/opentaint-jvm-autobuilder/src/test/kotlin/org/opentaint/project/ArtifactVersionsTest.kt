package org.opentaint.project

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class ArtifactVersionsTest {

    private fun assertGreater(left: String, right: String) {
        assertTrue(compareArtifactVersions(left, right) > 0, "expected $left > $right")
        assertTrue(compareArtifactVersions(right, left) < 0, "expected $right < $left")
    }

    @Test
    fun `numeric segments compare numerically, not lexicographically`() {
        assertGreater("1.10.0", "1.9.0")
        assertGreater("4.2.0", "4.0.10")
        assertEquals(0, compareArtifactVersions("1.2.3", "1.2.3"))
    }

    @Test
    fun `a longer numeric version is greater`() {
        assertGreater("1.2.1", "1.2")
    }

    @Test
    fun `a qualifier makes a version pre-release`() {
        assertGreater("4.2.0", "4.2.0-rc3")
        assertGreater("1.5.21", "1.5.21-SNAPSHOT")
        assertGreater("4.2.0-rc3", "4.0.10")
    }

    @Test
    fun `qualifiers compare to each other lexicographically`() {
        assertGreater("1.0-rc2", "1.0-beta1")
    }

    @Test
    fun `one version per artifact is kept, the highest`() {
        val deps = listOf(
            Triple("com.google.guava", "guava", "31.0"),
            Triple("ch.qos.logback", "logback-classic", "1.5.18"),
            Triple("com.google.guava", "guava", "33.2"),
            Triple("ch.qos.logback", "logback-classic", "1.5.21"),
            Triple("com.google.guava", "guava", "30.1"),
        )
        val dropped = mutableListOf<Triple<String, String, String>>()

        val kept = deps.singleVersionPerArtifact(
            artifact = { it.first to it.second },
            version = { it.third },
            onDropped = { _, d -> dropped += d }
        )

        assertEquals(
            listOf(
                Triple("com.google.guava", "guava", "33.2"),
                Triple("ch.qos.logback", "logback-classic", "1.5.21"),
            ),
            kept,
            "must keep the highest version of each artifact, in first-seen order"
        )
        assertEquals(3, dropped.size)
    }

    @Test
    fun `an unresolvable highest version falls back to the highest version that resolves`() {
        val deps = listOf(
            Triple("com.fasterxml.jackson.core", "jackson-core", "2.14.2"),
            Triple("com.fasterxml.jackson.core", "jackson-core", "2.17.3"),
            Triple("com.fasterxml.jackson.core", "jackson-core", "2.15.3"),
        )
        // 2.17.3 is in the dependency graph but was never downloaded: metadata only, no jar
        val jars = mapOf("2.14.2" to "jackson-core-2.14.2.jar", "2.15.3" to "jackson-core-2.15.3.jar")

        val kept = deps.singleResolvedVersionPerArtifact(
            artifact = { it.first to it.second },
            version = { it.third },
            resolve = { jars[it.third] },
        )

        assertEquals(
            listOf("jackson-core-2.15.3.jar"),
            kept,
            "an artifact whose highest version has no jar must still reach the model"
        )
    }

    @Test
    fun `an artifact that resolves at no version is dropped`() {
        val deps = listOf(Triple("com.example", "ghost", "1.0"), Triple("com.example", "ghost", "2.0"))

        val kept = deps.singleResolvedVersionPerArtifact(
            artifact = { it.first to it.second },
            version = { it.third },
            resolve = { null },
        )

        assertEquals(emptyList(), kept)
    }

    @Test
    fun `distinct artifacts of the same group are kept apart`() {
        val deps = listOf(
            Triple("org.springframework", "spring-core", "6.1.0"),
            Triple("org.springframework", "spring-web", "6.1.0"),
        )
        assertEquals(deps, deps.singleVersionPerArtifact({ it.first to it.second }, { it.third }))
    }
}
