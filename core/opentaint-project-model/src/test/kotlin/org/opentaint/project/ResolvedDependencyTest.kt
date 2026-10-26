package org.opentaint.project

import kotlin.io.path.Path
import kotlin.io.path.createTempFile
import kotlin.io.path.writeText
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

class ResolvedDependencyTest {
    @Test
    fun `mavenPurl formats a pkg-maven package-URL`() {
        assertEquals(
            "pkg:maven/org.opensearch.client/opensearch-rest-client@2.18.0",
            mavenPurl("org.opensearch.client", "opensearch-rest-client", "2.18.0"),
        )
    }

    @Test
    fun `relativeTo then resolve round-trips the path and keeps the purl`() {
        val abs = ResolvedDependency(
            path = Path("/repo/model/deps/opensearch-rest-client-2.18.0.jar"),
            purl = mavenPurl("org.opensearch.client", "opensearch-rest-client", "2.18.0"),
        )
        val rel = abs.relativeTo(Path("/repo/model"))
        assertEquals(Path("deps/opensearch-rest-client-2.18.0.jar"), rel.path)
        assertEquals("pkg:maven/org.opensearch.client/opensearch-rest-client@2.18.0", rel.purl)
        assertEquals(abs.path, rel.resolve(Path("/repo/model")).path)
    }

    @Test
    fun `purl is optional`() {
        val d = ResolvedDependency(path = Path("/x/lib.jar"))
        assertNull(d.purl)
    }

    @Test
    fun `a JavaProject serializes purl-tagged dependencies and loads them back`() {
        val jp = JavaProject(
            sourceRoot = Path("/p"),
            dependencies = listOf(
                ResolvedDependency(Path("/d/a.jar"), mavenPurl("g", "a", "1.0")),
            ),
        )
        val tmp = createTempFile(suffix = ".yaml")
        jp.dump(tmp)
        val loaded = JavaProject.load(tmp)
        val dep = loaded.dependencies.single()
        assertEquals(Path("/d/a.jar"), dep.path)
        assertEquals("pkg:maven/g/a@1.0", dep.purl)
    }

    @Test
    fun `a dependency without a purl round-trips`() {
        val jp = JavaProject(
            sourceRoot = Path("/p"),
            dependencies = listOf(ResolvedDependency(Path("/d/plain.jar"))),
        )
        val tmp = createTempFile(suffix = ".yaml")
        jp.dump(tmp)
        val loaded = JavaProject.load(tmp)
        val dep = loaded.dependencies.single()
        assertEquals(Path("/d/plain.jar"), dep.path)
        assertNull(dep.purl)
    }

    private val legacyJavaProjectYaml = """
        sourceRoot: /p
        dependencies:
        - /path/to/a.jar
        - /path/to/b.jar
    """.trimIndent()

    private val legacyProjectYaml = """
        projectRoot: /p
        javaProjects:
        - sourceRoot: /p
          dependencies:
          - /some/bare/path.jar
    """.trimIndent()

    @Test
    fun `JavaProject load accepts a legacy bare-string dependency as a path-only dependency`() {
        val tmp = createTempFile(suffix = ".yaml")
        tmp.writeText(legacyJavaProjectYaml)
        val loaded = JavaProject.load(tmp)
        assertEquals(
            listOf(Path("/path/to/a.jar"), Path("/path/to/b.jar")),
            loaded.dependencies.map { it.path },
        )
        loaded.dependencies.forEach { dep ->
            assertNull(dep.purl)
        }
    }

    @Test
    fun `Project load accepts a Project-shaped legacy bare-string dependency as a path-only dependency`() {
        val tmp = createTempFile(suffix = ".yaml")
        tmp.writeText(legacyProjectYaml)
        val loaded = Project.load(tmp)
        val dep = loaded.javaProjects.single().dependencies.single()
        assertEquals(Path("/some/bare/path.jar"), dep.path)
        assertNull(dep.purl)
    }
}
