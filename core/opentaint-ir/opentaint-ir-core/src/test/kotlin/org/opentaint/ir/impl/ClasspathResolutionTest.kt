package org.opentaint.ir.impl

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.opentaint.ir.api.jvm.ClassSource
import org.opentaint.ir.api.jvm.LocationType
import org.opentaint.ir.impl.fs.ClassSourceImpl
import org.opentaint.ir.testing.tree.DummyCodeLocation

class ClasspathResolutionTest {

    @Test
    fun `rank the union of vfs and persisted candidates`() {
        val runtime = DummyCodeLocation("runtime", LocationType.RUNTIME)
        val app = DummyCodeLocation("app", LocationType.APP)
        val lib = DummyCodeLocation("lib", LocationType.LIB)
        val resolution = ClasspathResolution(listOf(runtime, app, lib))

        val candidates = listOf(runtime.source(), lib.source(), app.source())
        candidates.permutations().forEach { permutation ->
            assertEquals(app, resolution.selectClassSource(permutation.asSequence())?.location)
        }
        assertEquals(lib, resolution.selectClassSource(sequenceOf(runtime.source(), lib.source()))?.location)
        assertEquals(runtime, resolution.selectClassSource(sequenceOf(runtime.source()))?.location)
    }

    @Test
    fun `use caller order for candidates with equal type`() {
        val first = DummyCodeLocation("first", LocationType.LIB)
        val second = DummyCodeLocation("second", LocationType.LIB)
        val resolution = ClasspathResolution(listOf(first, second))

        val selected = resolution.selectClassSource(sequenceOf(second.source(), first.source()))

        assertEquals(first, selected?.location)
    }

    @Test
    fun `deduplicate stores by registered location`() {
        val app = DummyCodeLocation("app", LocationType.APP)
        val lib = DummyCodeLocation("lib", LocationType.LIB)
        val resolution = ClasspathResolution(listOf(app, lib))
        val vfsApp = app.source(1)
        val persistedApp = app.source(2)
        val libSource = lib.source()

        val candidates = resolution.distinctClassSources(sequenceOf(vfsApp, persistedApp, libSource))

        assertEquals(listOf(vfsApp, libSource), candidates)
    }

    @Test
    fun `ignore candidates outside classpath`() {
        val app = DummyCodeLocation("app", LocationType.APP)
        val external = DummyCodeLocation("external", LocationType.APP)
        val resolution = ClasspathResolution(listOf(app))

        val selected = resolution.selectClassSource(sequenceOf(external.source(), app.source()))

        assertEquals(app, selected?.location)
    }

    private fun DummyCodeLocation.source(marker: Byte = 0): ClassSource = ClassSourceImpl(
        className = "duplicate.Type",
        location = this,
        byteCode = byteArrayOf(marker),
    )

    private fun <T> List<T>.permutations(): List<List<T>> = when {
        size <= 1 -> listOf(this)
        else -> indices.flatMap { index ->
            val selected = this[index]
            (take(index) + drop(index + 1)).permutations().map { listOf(selected) + it }
        }
    }
}
