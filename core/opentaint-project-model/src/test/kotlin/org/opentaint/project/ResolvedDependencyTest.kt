package org.opentaint.project

import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

class ResolvedDependencyTest {
    @Test
    fun `relativeTo then resolve round-trips the path and keeps coordinates`() {
        val abs = ResolvedDependency(
            path = Path("/repo/model/deps/opensearch-rest-client-2.18.0.jar"),
            group = "org.opensearch.client", artifact = "opensearch-rest-client", version = "2.18.0",
        )
        val rel = abs.relativeTo(Path("/repo/model"))
        assertEquals(Path("deps/opensearch-rest-client-2.18.0.jar"), rel.path)
        assertEquals("2.18.0", rel.version)
        assertEquals(abs.path, rel.resolve(Path("/repo/model")).path)
    }

    @Test
    fun `coordinates are optional`() {
        val d = ResolvedDependency(path = Path("/x/lib.jar"), group = null, artifact = null, version = null)
        assertNull(d.version)
    }

    @Test
    fun `a JavaProject serializes tagged dependencies and loads them back`() {
        val jp = JavaProject(
            sourceRoot = Path("/p"),
            dependencies = listOf(ResolvedDependency(Path("/d/a.jar"), "g", "a", "1.0")),
        )
        val tmp = kotlin.io.path.createTempFile(suffix = ".yaml")
        jp.dump(tmp)
        val loaded = JavaProject.load(tmp)
        assertEquals("1.0", loaded.dependencies.single().version)
        assertEquals(Path("/d/a.jar"), loaded.dependencies.single().path)
    }
}
