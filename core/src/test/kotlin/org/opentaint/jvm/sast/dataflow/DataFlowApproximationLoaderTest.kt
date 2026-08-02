package org.opentaint.jvm.sast.dataflow

import io.mockk.every
import io.mockk.mockk
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.JIRClasspath
import org.opentaint.ir.api.jvm.JIRDeclaration
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRInstLocation
import org.opentaint.jvm.sast.sarif.TraceMessageBuilder

class DataFlowApproximationLoaderTest {
    @Test
    fun `support classes loaded with approximations are analyzable`() {
        val location = mockk<RegisteredLocation> {
            every { path } returns "/tmp/compiled-approximations"
        }
        val declaration = mockk<JIRDeclaration> {
            every { this@mockk.location } returns location
        }
        val classpath = mockk<JIRClasspath> {
            every { features } returns listOf(
                DataFlowApproximationLoader.ApproximationLocations(
                    setOf("/tmp/compiled-approximations")
                )
            )
        }
        val supportClass = mockk<JIRClassOrInterface> {
            every { this@mockk.declaration } returns declaration
            every { this@mockk.classpath } returns classpath
        }
        val supportMethod = mockk<JIRMethod> {
            every { enclosingClass } returns supportClass
        }

        assertTrue(DataFlowApproximationLoader.isApproximation(supportMethod))
        assertTrue(DataFlowApproximationLoader.isApproximationLocation(classpath, location))

        val projectClasses = mockk<ClassLocationChecker> {
            every { isProjectLocation(any()) } returns false
        }
        val resolver = JIRTaintAnalyzer.Companion.PackageUnitResolver(classpath, projectClasses)
        assertFalse(resolver.locationIsUnknown(location))
    }

    @Test
    fun `support classes loaded with approximations are hidden from report traces`() {
        val approximationLocation = mockk<RegisteredLocation> {
            every { path } returns "/tmp/compiled-approximations"
        }
        val declaration = mockk<JIRDeclaration> {
            every { location } returns approximationLocation
        }
        val classpath = mockk<JIRClasspath> {
            every { features } returns listOf(
                DataFlowApproximationLoader.ApproximationLocations(
                    setOf("/tmp/compiled-approximations")
                )
            )
        }
        val supportClass = mockk<JIRClassOrInterface> {
            every { this@mockk.declaration } returns declaration
            every { this@mockk.classpath } returns classpath
        }
        val supportMethod = mockk<JIRMethod> {
            every { enclosingClass } returns supportClass
        }
        val instructionLocation = mockk<JIRInstLocation> {
            every { method } returns supportMethod
        }
        val instruction = mockk<JIRInst> {
            every { location } returns instructionLocation
        }

        assertTrue(TraceMessageBuilder.isGeneratedLocation(instruction))
    }
}
