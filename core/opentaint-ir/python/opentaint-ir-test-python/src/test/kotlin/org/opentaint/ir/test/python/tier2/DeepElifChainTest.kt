package org.opentaint.ir.test.python.tier2

import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Tag
import org.opentaint.ir.api.python.*
import org.opentaint.ir.test.python.PIRTestBase

@Tag("tier2")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class DeepElifChainTest : PIRTestBase() {

    private lateinit var cp: PIRClasspath

    companion object {
        const val BRANCHES = 120

        val SOURCE = buildString {
            appendLine("def dispatch(op, value):")
            appendLine("    result = 0")
            for (i in 0 until BRANCHES) {
                appendLine("    ${if (i == 0) "if" else "elif"} op == \"op$i\":")
                appendLine("        result = value + $i")
            }
            appendLine("    else:")
            appendLine("        result = -1")
            appendLine("    return result")
        }
    }

    @BeforeAll fun setup() { cp = buildFromSource(SOURCE) }

    private val dispatch get() = cp.findFunctionOrNull("__test__.dispatch")!!

    @Test fun `deep elif chain survives serialization`() {
        assertNotNull(cp.findFunctionOrNull("__test__.dispatch"),
            "function must not be dropped by protobuf nesting limits")
        assertTrue(cp.findModuleOrNull("__test__")!!.diagnostics.none {
            it.severity == PIRDiagnosticSeverity.ERROR
        }, "no serialization errors expected")
    }

    @Test fun `every branch is lowered`() {
        val branches = dispatch.instList.count { it is PIRBranch }
        assertEquals(BRANCHES, branches,
            "expected one branch per elif arm")
    }

    @Test fun `every block is reachable from entry`() {
        val cfg = dispatch.cfg
        val reachable = mutableSetOf(cfg.entryBlock.label)
        val queue = ArrayDeque(listOf(cfg.entryBlock))
        while (queue.isNotEmpty()) {
            val block = queue.removeFirst()
            for (succ in cfg.successors(block) + cfg.exceptionalSuccessors(block)) {
                if (reachable.add(succ.label)) queue.add(succ)
            }
        }
        assertEquals(cfg.blocks.size, reachable.size,
            "unreachable blocks: ${cfg.blocks.map { it.label }.toSet() - reachable}")
    }

    @Test fun `each arm keeps its own source line`() {
        val lines = dispatch.instList
            .filterIsInstance<PIRBranch>()
            .mapNotNull { it.physicalLocation?.lineStart }
        assertEquals(lines.size, lines.toSet().size,
            "collapsing the elif chain must not collapse branch locations onto one line")
    }
}
