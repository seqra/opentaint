package org.opentaint.ir.testing

import org.opentaint.ir.api.jvm.ByteCodeLocationSpec
import org.opentaint.ir.api.jvm.JIRSettings
import org.opentaint.ir.api.jvm.JavaVersion
import org.opentaint.ir.api.jvm.LocationType
import org.opentaint.ir.impl.fs.BuildFolderLocation
import org.opentaint.ir.impl.fs.JarLocation
import org.opentaint.ir.impl.fs.createByteCodeLocations
import org.opentaint.ir.impl.fs.dirOrJarAsBytecodeLocation
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.io.TempDir
import java.io.File
import java.io.FileOutputStream
import java.nio.file.Path
import java.util.jar.Attributes
import java.util.jar.JarOutputStream
import java.util.jar.Manifest

class LocationTypeTest {

    @TempDir
    lateinit var tempDir: Path

    private val javaVersion = object : JavaVersion {
        override val majorVersion: Int = 17
    }

    @Test
    fun `settings retain typed bytecode specs and default legacy inputs to app`() {
        val app = File("app")
        val library = File("library")

        val settings = JIRSettings()
            .loadByteCode(listOf(app))
            .loadByteCode(listOf(library), LocationType.LIB)

        assertEquals(
            listOf(
                ByteCodeLocationSpec(app, LocationType.APP),
                ByteCodeLocationSpec(library, LocationType.LIB),
            ),
            settings.predefinedByteCodeLocations,
        )
    }

    @Test
    fun `build folder retains its type through refresh and equality`() {
        val directory = tempDir.resolve("classes").toFile().apply { mkdir() }
        val library = BuildFolderLocation(directory, LocationType.LIB)

        assertEquals(LocationType.LIB, library.type)
        assertEquals(LocationType.LIB, library.createRefreshed().type)
        assertEquals(library, BuildFolderLocation(directory, LocationType.LIB))
        assertNotEquals(library, BuildFolderLocation(directory, LocationType.APP))
    }

    @Test
    fun `location type does not change artifact file system identity`() {
        val directory = tempDir.resolve("classes-identity").toFile().apply {
            mkdir()
            resolve("content.class").writeBytes(byteArrayOf(1, 2, 3))
        }
        val jar = tempDir.resolve("identity.jar").toFile().also { createJar(it) }

        assertEquals(
            BuildFolderLocation(directory, LocationType.APP).fileSystemId,
            BuildFolderLocation(directory, LocationType.LIB).fileSystemId,
        )
        assertEquals(
            JarLocation(jar, LocationType.APP, javaVersion).fileSystemId,
            JarLocation(jar, LocationType.LIB, javaVersion).fileSystemId,
        )
    }

    @Test
    fun `jar and manifest classpath entries inherit the requested type`() {
        val dependency = tempDir.resolve("dependency.jar").toFile().also { createJar(it) }
        val root = tempDir.resolve("root.jar").toFile().also {
            createJar(it, "file:${dependency.absolutePath}")
        }

        val locations = root.dirOrJarAsBytecodeLocation(javaVersion, LocationType.LIB)

        assertEquals(setOf(root.absolutePath, dependency.absolutePath), locations.map { it.path }.toSet())
        assertEquals(setOf(LocationType.LIB), locations.map { it.type }.toSet())
        assertEquals(setOf(LocationType.LIB), locations.mapNotNull { it.createRefreshed()?.type }.toSet())
    }

    @Test
    fun `typed conversion does not collapse conflicting roles before registry validation`() {
        val library = tempDir.resolve("library.jar").toFile().also { createJar(it) }

        val locations = listOf(
            ByteCodeLocationSpec(library, LocationType.APP),
            ByteCodeLocationSpec(library, LocationType.LIB),
        ).createByteCodeLocations(javaVersion)

        assertEquals(listOf(LocationType.APP, LocationType.LIB), locations.map { it.type })
        assertNotEquals(
            JarLocation(library, LocationType.APP, javaVersion),
            JarLocation(library, LocationType.LIB, javaVersion),
        )
    }

    private fun createJar(file: File, classPath: String? = null) {
        val manifest = Manifest().apply {
            mainAttributes[Attributes.Name.MANIFEST_VERSION] = "1.0"
            classPath?.let { mainAttributes[Attributes.Name.CLASS_PATH] = it }
        }
        JarOutputStream(FileOutputStream(file), manifest).use { }
    }
}
