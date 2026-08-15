package org.opentaint.ir.testing

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.api.io.TempDir
import org.opentaint.ir.api.jvm.JIRDatabase
import org.opentaint.ir.api.jvm.JIRPersistenceImplSettings
import org.opentaint.ir.api.jvm.LocationType
import org.opentaint.ir.impl.JIRRamErsSettings
import org.opentaint.ir.impl.JIRSQLitePersistenceSettings
import org.opentaint.ir.impl.fs.BuildFolderLocation
import org.opentaint.ir.impl.opentaintIrDb
import java.io.File
import java.nio.file.Path

class LocationRegistrationTest {

    @TempDir
    lateinit var tempDir: Path

    @Test
    fun `classpath reuses the registered library type`() {
        val location = classesDirectory()
        val db = database(location, LocationType.LIB)

        try {
            val classpath = runBlocking { db.classpath(listOf(location)) }
            try {
                assertEquals(LocationType.LIB, db.locations.single().type)
                val registeredLocation = classpath.registeredLocations.single()
                assertEquals(LocationType.LIB, registeredLocation.type)
                assertEquals(LocationType.LIB, registeredLocation.jIRLocation?.type)
                assertEquals(LocationType.LIB, classpath.locations.single().type)
            } finally {
                classpath.close()
            }
        } finally {
            db.close()
        }
    }

    @Test
    fun `classpath registers an unknown artifact as app`() {
        val location = classesDirectory()
        val db = database()

        try {
            runBlocking { db.classpath(listOf(location)) }.use { classpath ->
                assertEquals(LocationType.APP, db.locations.single().type)
                assertEquals(LocationType.APP, classpath.registeredLocations.single().type)
            }
        } finally {
            db.close()
        }
    }

    @Test
    fun `registration rejects a different type for the same artifact`() {
        val location = classesDirectory()
        val db = database(location, LocationType.LIB)

        try {
            val error = assertThrows<IllegalArgumentException> {
                runBlocking { db.load(listOf(location), LocationType.APP) }
            }

            assertTrue(error.message.orEmpty().contains("type conflict"))
            assertTrue(error.message.orEmpty().contains("LIB"))
            assertTrue(error.message.orEmpty().contains("APP"))
        } finally {
            db.close()
        }
    }

    @Test
    fun `conflicting types in one batch fail without registration`() {
        val location = classesDirectory()
        val db = database()

        try {
            assertThrows<IllegalArgumentException> {
                runBlocking {
                    db.loadLocations(
                        listOf(
                            BuildFolderLocation(location, LocationType.APP),
                            BuildFolderLocation(location, LocationType.LIB),
                        )
                    )
                }
            }
            assertTrue(db.locations.isEmpty())
        } finally {
            db.close()
        }
    }

    @Test
    fun `database identity includes the registered type`() {
        val location = classesDirectory()
        val appDb = database(location, LocationType.APP)
        val libDb = database(location, LocationType.LIB)

        try {
            assertNotEquals(appDb.id, libDb.id)
        } finally {
            appDb.close()
            libDb.close()
        }
    }

    @Test
    fun `classpath lookup prefers app then library then runtime`() {
        val runtime = classesDirectory("runtime")
        val library = classesDirectory("library")
        val app = classesDirectory("app")
        val className = javaClass.name
        listOf(runtime, library, app).forEach { directory ->
            copyTestClass(directory, className)
            directory.resolve("identity.marker").writeText(directory.name)
        }

        val db = runBlocking {
            opentaintIrDb {
                persistenceImpl(JIRRamErsSettings)
                buildModelForJRE(false)
                loadByteCode(listOf(runtime), LocationType.RUNTIME)
                loadByteCode(listOf(library), LocationType.LIB)
                loadByteCode(listOf(app), LocationType.APP)
            }.also { it.awaitBackgroundJobs() }
        }

        try {
            runBlocking { db.classpath(listOf(runtime, library, app)) }.use { classpath ->
                assertEquals(
                    LocationType.APP,
                    requireNotNull(classpath.findClassOrNull(className)).declaration.location.type,
                )
            }
            runBlocking { db.classpath(listOf(runtime, library)) }.use { classpath ->
                assertEquals(
                    LocationType.LIB,
                    requireNotNull(classpath.findClassOrNull(className)).declaration.location.type,
                )
            }
        } finally {
            db.close()
        }
    }

    @Test
    fun `sqlite persistence restores the registered location type`() {
        val location = classesDirectory()
        val databaseFile = tempDir.resolve("locations.sqlite").toFile()
        database(
            location,
            LocationType.LIB,
            JIRSQLitePersistenceSettings,
            databaseFile.absolutePath,
        ).close()

        val restored = database(
            persistenceSettings = JIRSQLitePersistenceSettings,
            persistencePath = databaseFile.absolutePath,
        )
        try {
            assertEquals(LocationType.LIB, restored.locations.single().type)
        } finally {
            restored.close()
        }
    }

    @Test
    fun `refresh creates a new sqlite identity without changing the library type`() {
        assertRefreshPreservesType(JIRSQLitePersistenceSettings, tempDir.resolve("refresh.sqlite").toString())
    }

    @Test
    fun `refresh creates a new ers identity without changing the library type`() {
        assertRefreshPreservesType(JIRRamErsSettings)
    }

    private fun assertRefreshPreservesType(
        persistenceSettings: JIRPersistenceImplSettings,
        persistencePath: String? = null,
    ) {
        val location = classesDirectory("refresh-classes")
        val db = database(location, LocationType.LIB, persistenceSettings, persistencePath)
        val classpath = runBlocking { db.classpath(listOf(location)) }

        try {
            location.resolve("content.marker").writeText("changed")
            runBlocking {
                db.refresh()
                db.awaitBackgroundJobs()
            }

            assertEquals(2, db.locations.size)
            assertEquals(setOf(LocationType.LIB), db.locations.map { it.type }.toSet())
            assertEquals(2, db.locations.map { it.id }.toSet().size)
            assertEquals(2, db.locations.mapNotNull { it.jIRLocation?.fileSystemId }.toSet().size)
        } finally {
            classpath.close()
            db.close()
        }
    }

    private fun classesDirectory(name: String = "classes"): File = tempDir.resolve(name).toFile().apply { mkdir() }

    private fun copyTestClass(directory: File, className: String) {
        val relativePath = className.replace('.', '/') + ".class"
        val bytes = requireNotNull(javaClass.classLoader.getResourceAsStream(relativePath)).use { it.readBytes() }
        directory.resolve(relativePath).apply {
            parentFile.mkdirs()
            writeBytes(bytes)
        }
    }

    private fun database(
        location: File? = null,
        type: LocationType = LocationType.APP,
        persistenceSettings: JIRPersistenceImplSettings = JIRRamErsSettings,
        persistencePath: String? = null,
    ): JIRDatabase = runBlocking {
        opentaintIrDb {
            persistencePath?.let { persistent(it) }
            persistenceImpl(persistenceSettings)
            buildModelForJRE(false)
            location?.let { loadByteCode(listOf(it), type) }
        }.also { it.awaitBackgroundJobs() }
    }
}
