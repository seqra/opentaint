package org.opentaint.project

import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals

class MavenResolvedDependencyTest {
    @Test
    fun `resolved maven artifacts carry coordinates`() {
        val r = MavenProjectResolver.MavenDependencyGraphResolver()
        r.addDependencies(mavenGraphWith(group = "com.fasterxml.jackson.core",
            artifact = "jackson-core", version = "2.17.3"))
        val deps = r.resolveDependencies(resolvePath = { Path("/m2/${it.artifactId}-${it.version}.jar") })
        val jc = deps.single { it.artifact == "jackson-core" }
        assertEquals("2.17.3", jc.version)
        assertEquals(Path("/m2/jackson-core-2.17.3.jar"), jc.path)
    }

    private fun mavenGraphWith(group: String, artifact: String, version: String): MavenProjectResolver.MavenDependencies {
        val id = "$group:$artifact:jar:$version"
        return MavenProjectResolver.MavenDependencies(
            artifacts = listOf(
                MavenProjectResolver.MavenArtifact(
                    id = id,
                    groupId = group,
                    artifactId = artifact,
                    version = version,
                )
            ),
            dependencies = listOf(
                MavenProjectResolver.MavenDependency(from = "root", to = id),
            ),
        )
    }
}
