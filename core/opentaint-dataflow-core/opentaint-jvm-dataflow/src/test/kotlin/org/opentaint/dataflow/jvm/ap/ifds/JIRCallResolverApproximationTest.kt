package org.opentaint.dataflow.jvm.ap.ifds

import io.mockk.every
import io.mockk.mockk
import org.junit.jupiter.api.Assertions.assertSame
import org.junit.jupiter.api.Test
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.JIRMethod

class JIRCallResolverApproximationTest {
    @Test
    fun `unresolved concrete override falls back to interface approximation`() {
        val approximation = mockk<JIRMethod> {
            every { name } returns "convert"
            every { description } returns "(Ljava/lang/String;)Ljava/lang/String;"
        }
        val modeledInterface = mockk<JIRClassOrInterface> {
            every { superClass } returns null
            every { interfaces } returns emptyList()
            every { declaredMethods } returns listOf(approximation)
        }
        val concreteClass = mockk<JIRClassOrInterface> {
            every { superClass } returns null
            every { interfaces } returns listOf(modeledInterface)
        }
        val concreteOverride = mockk<JIRMethod> {
            every { name } returns "convert"
            every { description } returns "(Ljava/lang/String;)Ljava/lang/String;"
            every { enclosingClass } returns concreteClass
        }
        val unitResolver = mockk<JIRUnitResolver> {
            every { isApproximation(approximation) } returns true
        }

        assertSame(approximation, concreteOverride.findApproximationOverride(unitResolver))
    }
}
