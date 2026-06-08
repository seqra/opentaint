package org.opentaint.ir.go.test.features

import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.extension.ExtendWith
import org.opentaint.ir.go.ext.findFunctionByName
import org.opentaint.ir.go.api.GoIRBody
import org.opentaint.ir.go.impl.GoIRBasicBlockImpl
import org.opentaint.ir.go.inst.GoIRIf
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.inst.GoIRInstRef
import org.opentaint.ir.go.inst.GoIRJump
import org.opentaint.ir.go.inst.block
import org.opentaint.ir.go.inst.index
import org.opentaint.ir.go.test.GoIRSanityChecker
import org.opentaint.ir.go.test.GoIRTestBuilder
import org.opentaint.ir.go.test.GoIRTestExtension

/**
 * Negative sanity tests for explicit branch instruction targets.
 */
@ExtendWith(GoIRTestExtension::class)
class BranchTargetSanityTests {

    @Test
    fun `sanity checker reports out-of-range jump target`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource("""
            package p
            func sum(n int) int {
                s := 0
                for i := 0; i < n; i++ {
                    s += i
                }
                return s
            }
        """.trimIndent())
        val body = prog.findFunctionByName("sum")!!.body!!
        val jump = body.instructions.filterIsInstance<GoIRJump>().first()
        val badJump = jump.copy(target = GoIRInstRef(body.instructions.size + 1))
        replaceInst(body, jump.index, badJump)

        val result = GoIRSanityChecker.check(prog, deep = false)

        assertThat(result.errors.map { it.message })
            .anySatisfy { assertThat(it).contains("Jump target", "outside instruction range") }
    }

    @Test
    fun `sanity checker reports mismatched if branch target`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource("""
            package p
            func abs(x int) int {
                if x < 0 { return -x }
                return x
            }
        """.trimIndent())
        val body = prog.findFunctionByName("abs")!!.body!!
        val ifInst = body.instructions.filterIsInstance<GoIRIf>().first()
        val badIf = ifInst.copy(trueBranch = ifInst.falseBranch)
        replaceInst(body, ifInst.index, badIf)

        val result = GoIRSanityChecker.check(prog, deep = false)

        assertThat(result.errors.map { it.message })
            .anySatisfy { assertThat(it).contains("If trueBranch", "expected successor block") }
    }

    private fun replaceInst(body: GoIRBody, index: Int, replacement: GoIRInst) {
        val block = body.instructions[index].block as GoIRBasicBlockImpl
        block.setInstructions(block.instructions.map { if (it.index == index) replacement else it })
    }
}
