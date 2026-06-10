package org.opentaint.ir.go.test.features

import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.extension.ExtendWith
import org.opentaint.ir.go.ext.findFunctionByName
import org.opentaint.ir.go.ext.findInstructions
import org.opentaint.ir.go.inst.GoIRFieldStore
import org.opentaint.ir.go.inst.GoIRIndexStore
import org.opentaint.ir.go.inst.GoIRStore
import org.opentaint.ir.go.test.GoIRSanityChecker
import org.opentaint.ir.go.test.GoIRTestBuilder
import org.opentaint.ir.go.test.GoIRTestExtension

@ExtendWith(GoIRTestExtension::class)
class StoreSpecializationTests {

    private val source = """
        package p

        type Point struct {
            X int
            Y int
        }

        func setField(p *Point, v int) {
            p.Y = v
        }

        func setIndex(s []int, v int) {
            s[1] = v
        }

        func setPtr(p *int, v int) {
            *p = v
        }
    """.trimIndent()

    @Test
    fun `field store is specialized to GoIRFieldStore`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource(source)
        val fn = prog.findFunctionByName("setField")!!

        val fieldStores = fn.findInstructions<GoIRFieldStore>()
        assertThat(fieldStores).hasSize(1)
        assertThat(fieldStores[0].fieldName).isEqualTo("Y")
        assertThat(fieldStores[0].fieldIndex).isEqualTo(1)

        assertThat(fn.findInstructions<GoIRStore>()).isEmpty()

        GoIRSanityChecker.check(prog).assertNoErrors()
    }

    @Test
    fun `index store is specialized to GoIRIndexStore`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource(source)
        val fn = prog.findFunctionByName("setIndex")!!

        assertThat(fn.findInstructions<GoIRIndexStore>()).hasSize(1)
        assertThat(fn.findInstructions<GoIRStore>()).isEmpty()
    }

    @Test
    fun `store through a plain pointer stays a generic GoIRStore`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource(source)
        val fn = prog.findFunctionByName("setPtr")!!

        assertThat(fn.findInstructions<GoIRStore>()).hasSize(1)
        assertThat(fn.findInstructions<GoIRFieldStore>()).isEmpty()
        assertThat(fn.findInstructions<GoIRIndexStore>()).isEmpty()
    }
}
