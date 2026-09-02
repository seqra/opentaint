package org.opentaint.ir.test.python.tier2

import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Tag
import org.opentaint.ir.api.python.*
import org.opentaint.ir.test.python.PIRTestBase

@Tag("tier2")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class MatchPatternLoweringTest : PIRTestBase() {

    private lateinit var cp: PIRClasspath

    companion object {
        val SOURCE = """
class MpDevice:
    pass

class MpGroup:
    pass

def mp_class_only(instance: object) -> str:
    match instance:
        case MpDevice():
            return "device"
        case MpGroup():
            return "group"

def mp_sequence_only(a: int, b: int) -> str:
    match (a, b):
        case (0, 1):
            return "zero-one"
        case (_, 1):
            return "any-one"
        case (0, _):
            return "zero-any"

def mp_mapping_only(data: dict) -> str:
    match data:
        case {"issue": issue}:
            return "issue"
        case {"event": event}:
            return "event"

def mp_starred_only(items: list) -> str:
    match items:
        case [str(), *rest]:
            return "strings"
        case [int(), *rest]:
            return "ints"

def mp_mixed(v: object) -> str:
    match v:
        case [1, 2]:
            return "pair"
        case str():
            return "text"
        case _:
            return "other"

def mp_class_subpatterns(v: object) -> str:
    match v:
        case str(s):
            return "positional"
        case MpDevice(name=n):
            return "keyword"
        case MpGroup() as g:
            return "as-binding"
        case _:
            return "other"
        """.trimIndent()
    }

    @BeforeAll fun setup() { cp = buildFromSource(SOURCE) }
    @AfterAll fun tearDown() { cp.close() }

    private fun func(name: String): PIRFunction =
        cp.findFunctionOrNull("__test__.$name") ?: fail("Function __test__.$name not found")

    private val matchFunctions = listOf(
        "mp_class_only", "mp_sequence_only", "mp_mapping_only", "mp_starred_only", "mp_mixed",
        "mp_class_subpatterns",
    )

    private fun reachableBlocks(cfg: PIRCFG): Set<Int> {
        val visited = mutableSetOf(cfg.entryBlock.label)
        val queue = ArrayDeque<PIRBasicBlock>()
        queue.add(cfg.entryBlock)
        while (queue.isNotEmpty()) {
            val block = queue.removeFirst()
            for (succ in cfg.successors(block) + cfg.exceptionalSuccessors(block)) {
                if (visited.add(succ.label)) queue.add(succ)
            }
        }
        return visited
    }

    @Test
    fun `every block is terminated`() {
        for (name in matchFunctions) {
            val f = func(name)
            for (block in f.cfg.blocks) {
                assertDoesNotThrow({ f.cfg.successors(block) },
                    "$name: block ${block.label} ends with " +
                        "${block.instructions.lastOrNull()?.let { it::class.simpleName }}")
            }
        }
    }

    @Test
    fun `every case body is reachable`() {
        val expected = mapOf(
            "mp_class_only" to setOf("device", "group"),
            "mp_sequence_only" to setOf("zero-one", "any-one", "zero-any"),
            "mp_mapping_only" to setOf("issue", "event"),
            "mp_starred_only" to setOf("strings", "ints"),
            "mp_mixed" to setOf("pair", "text", "other"),
            "mp_class_subpatterns" to setOf("positional", "keyword", "as-binding", "other"),
        )
        for ((name, bodies) in expected) {
            val cfg = func(name).cfg
            val reachable = reachableBlocks(cfg)
            val reached = cfg.blocks
                .filter { it.label in reachable }
                .flatMap { it.instructions }
                .filterIsInstance<PIRReturn>()
                .mapNotNull { (it.value as? PIRStrConst)?.value }
                .toSet()
            assertEquals(bodies, reached, "$name: case bodies missing or unreachable")
        }
    }

    @Test
    fun `class patterns lower to a type check per case`() {
        val checks = func("mp_class_only").instList
            .filterIsInstance<PIRAssign>()
            .mapNotNull { (it.expr as? PIRTypeCheckExpr)?.checkType }
            .filterIsInstance<PIRClassType>()
            .map { it.qualifiedName }
        assertEquals(listOf("__test__.MpDevice", "__test__.MpGroup"), checks)
    }

    @Test
    fun `unsupported patterns lower to an opaque type check`() {
        for (name in listOf("mp_sequence_only", "mp_mapping_only", "mp_starred_only")) {
            val opaque = func(name).instList
                .filterIsInstance<PIRAssign>()
                .count { (it.expr as? PIRTypeCheckExpr)?.checkType == PIRAnyType }
            assertTrue(opaque > 0, "$name: no opaque pattern test emitted")
        }
    }

    @Test
    fun `class pattern sub-patterns are ignored and only the type check is emitted`() {
        val f = func("mp_class_subpatterns")
        val checks = f.instList
            .filterIsInstance<PIRAssign>()
            .mapNotNull { (it.expr as? PIRTypeCheckExpr)?.checkType }
        assertEquals(
            listOf("__test__.MpDevice", "__test__.MpGroup", "builtins.str"),
            checks.map { it.toString() }.sorted(),
        )
        assertTrue(f.instList.filterIsInstance<PIRLoadAttr>().isEmpty(),
            "class pattern sub-patterns must not be lowered as attribute loads")
    }

    @Test
    fun `outer as binding on a class pattern still binds the subject`() {
        val bound = func("mp_class_subpatterns").instList
            .filterIsInstance<PIRAssign>()
            .mapNotNull { (it.target as? PIRLocalVar)?.name }
        assertTrue("g" in bound, "expected `case MpGroup() as g` to bind g; bound: $bound")
        assertFalse("n" in bound, "keyword sub-pattern capture must not be bound")
        assertFalse("s" in bound, "positional sub-pattern capture must not be bound")
    }

    @Test
    fun `unsupported patterns are reported as warnings`() {
        val warnings = cp.modules.first().diagnostics
            .filter { it.severity == PIRDiagnosticSeverity.WARNING }
        val kinds = warnings.map { it.message.substringAfter("pattern ").substringBefore(";") }.toSet()
        assertEquals(setOf("SequencePattern", "MappingPattern"), kinds)
        assertTrue(warnings.all { it.exceptionType == "UnsupportedMatchPattern" })
    }
}
