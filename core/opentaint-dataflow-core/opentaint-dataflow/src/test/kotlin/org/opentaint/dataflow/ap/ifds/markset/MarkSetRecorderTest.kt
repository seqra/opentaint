package org.opentaint.dataflow.ap.ifds.markset

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import java.util.concurrent.CountDownLatch
import java.util.concurrent.Executors
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class MarkSetRecorderTest {
    private data class FakeMethod(override val name: String) : CommonMethod {
        override val parameters: List<CommonMethodParameter> = emptyList()
        override val returnType: CommonTypeName get() = error("Unsupported")
        override fun flowGraph(): ControlFlowGraph<CommonInst> = error("Unsupported")
    }

    private class FakeLocation(override val method: CommonMethod, override val index: Int) : CommonInstLocation

    private class FakeInst(override val location: CommonInstLocation) : CommonInst

    private class FakeRule : CommonTaintConfigurationItem

    private fun inst(method: CommonMethod, index: Int = 0): CommonInst = FakeInst(FakeLocation(method, index))

    private fun position(argIdx: Int): PositionAccess = PositionAccess.Simple(AccessPathBase.Argument(argIdx))

    private fun literal(
        markName: String,
        position: PositionAccess,
        negated: Boolean = false,
        anyAccessor: Boolean = false,
    ): RuleConditionRewriter.ExprOrConstant {
        val accessor = TaintMarkAccessor(markName)
        val expr = if (anyAccessor) {
            TaintMarkAwareConditionExpr.ContainsMarkOnAnyAccessorLiteral(position, accessor, negated)
        } else {
            TaintMarkAwareConditionExpr.ContainsMarkLiteral(position, accessor, negated)
        }
        return RuleConditionRewriter.ExprOrConstant(expr)
    }

    private fun and(parts: List<RuleConditionRewriter.ExprOrConstant>): RuleConditionRewriter.ExprOrConstant {
        val exprs = parts.map { it.expr }.toTypedArray()
        return RuleConditionRewriter.ExprOrConstant(TaintMarkAwareConditionExpr.And(exprs))
    }

    @Test
    fun `an inactive recorder records nothing`() {
        val recorder = MarkSetRecorder()
        val caller = FakeMethod("caller")
        val callee = FakeMethod("callee")
        val statement = inst(caller)
        val rule = FakeRule()

        // active defaults to false.
        recorder.recordEdge(caller, statement, callee)
        recorder.recordStatement(statement)
        recorder.recordSite(statement, rule, SiteKind.SOURCE, RuleConditionRewriter.trueExpr, gens = listOf("A"))
        recorder.recordCleaner(statement, literal("A", position(0)))

        val input = recorder.seal(roots = listOf(caller))

        assertEquals(0, input.program.methodCount)
        assertEquals(0, input.program.sites.size)
        assertEquals(0, input.markNames.size)
        assertTrue(input.coveredStatements.isEmpty())
        assertTrue(input.program.cleanerAtoms.isEmpty)
        assertFalse(recorder.overflow)
    }

    @Test
    fun `negated literals become True`() {
        val recorder = MarkSetRecorder()
        recorder.active = true
        val method = FakeMethod("m")
        val statement = inst(method)
        val rule = FakeRule()

        recorder.recordSite(
            statement,
            rule,
            SiteKind.SINK,
            literal("A", position(0), negated = true),
            gens = emptyList(),
        )

        val input = recorder.seal(roots = emptyList())
        assertEquals(1, input.program.sites.size)
        assertEquals(MarkCond.True, input.program.sites.single().cond)
    }

    @Test
    fun `A at arg0 and A at arg1 gets two literal ids so the cube is joined`() {
        val recorder = MarkSetRecorder()
        recorder.active = true
        val method = FakeMethod("m")
        val statement = inst(method)
        val rule = FakeRule()

        val residual = and(listOf(literal("A", position(0)), literal("A", position(1))))
        recorder.recordSite(statement, rule, SiteKind.SOURCE, residual, gens = listOf("A"))

        val input = recorder.seal(roots = emptyList())
        val cond = input.program.sites.single().cond
        check(cond is MarkCond.And)
        val literals = cond.args.filterIsInstance<MarkCond.Lit>()
        assertEquals(2, literals.size)
        assertEquals(setOf(literals[0].mark), setOf(literals[1].mark)) // same mark id...
        assertTrue(literals[0].literal != literals[1].literal) // ...but two distinct literal ids
        assertTrue(cond.hasJoinedCube())
    }

    @Test
    fun `dedup - recording the same site twice keeps one`() {
        val recorder = MarkSetRecorder()
        recorder.active = true
        val method = FakeMethod("m")
        val statement = inst(method)
        val rule = FakeRule()
        val residual = literal("A", position(0))

        recorder.recordSite(statement, rule, SiteKind.SOURCE, residual, gens = listOf("A"))
        recorder.recordSite(statement, rule, SiteKind.SOURCE, residual, gens = listOf("A"))

        val input = recorder.seal(roots = emptyList())
        assertEquals(1, input.program.sites.size)
    }

    @Test
    fun `two residuals for the same statement and rule are both kept`() {
        val recorder = MarkSetRecorder()
        recorder.active = true
        val method = FakeMethod("m")
        val statement = inst(method)
        val rule = FakeRule()

        recorder.recordSite(statement, rule, SiteKind.SOURCE, literal("A", position(0)), gens = listOf("A"))
        recorder.recordSite(statement, rule, SiteKind.SOURCE, literal("B", position(0)), gens = listOf("B"))

        val input = recorder.seal(roots = emptyList())
        assertEquals(2, input.program.sites.size)
    }

    @Test
    fun `a false residual is not recorded`() {
        val recorder = MarkSetRecorder()
        recorder.active = true
        val method = FakeMethod("m")
        val statement = inst(method)
        val rule = FakeRule()

        recorder.recordSite(statement, rule, SiteKind.SOURCE, RuleConditionRewriter.falseExpr, gens = emptyList())

        val input = recorder.seal(roots = emptyList())
        assertEquals(0, input.program.sites.size)
    }

    @Test
    fun `the cap sets overflow`() {
        val recorder = MarkSetRecorder(maxSites = 1)
        recorder.active = true
        val method = FakeMethod("m")
        val rule = FakeRule()

        recorder.recordSite(inst(method, 0), rule, SiteKind.SOURCE, literal("A", position(0)), gens = emptyList())
        assertFalse(recorder.overflow)
        recorder.recordSite(inst(method, 1), rule, SiteKind.SOURCE, literal("B", position(0)), gens = emptyList())
        assertTrue(recorder.overflow)

        val input = recorder.seal(roots = emptyList())
        assertEquals(1, input.program.sites.size)
    }

    @Test
    fun `the edge cap sets overflow`() {
        val recorder = MarkSetRecorder(maxEdges = 1)
        recorder.active = true
        val caller = FakeMethod("caller")
        val calleeA = FakeMethod("calleeA")
        val calleeB = FakeMethod("calleeB")
        val call = inst(caller)

        recorder.recordEdge(caller, call, calleeA)
        assertFalse(recorder.overflow)
        recorder.recordEdge(caller, call, calleeB)
        assertTrue(recorder.overflow)
    }

    @Test
    fun `seal builds callees, roots and the site to SiteRef alignment`() {
        val recorder = MarkSetRecorder()
        recorder.active = true
        val root = FakeMethod("root")
        val mid = FakeMethod("mid")
        val leaf = FakeMethod("leaf")
        val unrelated = FakeMethod("unrelated") // never recorded: not a known method

        recorder.recordEdge(root, inst(root, 0), mid)
        recorder.recordEdge(mid, inst(mid, 0), leaf)
        recorder.recordEdge(mid, inst(mid, 0), leaf) // duplicate edge, deduplicated

        val sourceStatement = inst(root, 1)
        val sinkStatement = inst(leaf, 1)
        val sourceRule = FakeRule()
        val sinkRule = FakeRule()
        recorder.recordSite(
            sourceStatement,
            sourceRule,
            SiteKind.SOURCE,
            RuleConditionRewriter.trueExpr,
            gens = listOf("TAINT"),
        )
        recorder.recordSite(sinkStatement, sinkRule, SiteKind.SINK, literal("TAINT", position(0)), gens = emptyList())
        recorder.recordStatement(sourceStatement)
        recorder.recordStatement(sinkStatement)

        val input = recorder.seal(roots = listOf(root, unrelated))
        val program = input.program

        assertEquals(3, program.methodCount) // root, mid, leaf
        assertEquals(1, program.roots.size)
        assertEquals(2, program.sites.size)
        assertEquals(2, input.sites.size)
        assertEquals(setOf(sourceStatement, sinkStatement), input.coveredStatements)
        assertEquals(listOf("TAINT"), input.markNames)

        val rootId = program.roots.single()
        assertEquals(1, program.callees[rootId].size) // root -> mid, once

        // site <-> SiteRef alignment, by index.
        for (i in program.sites.indices) {
            val site = program.sites[i]
            val ref = input.sites[i]
            if (site.kind == SiteKind.SOURCE) {
                assertEquals(sourceStatement, ref.statement)
                assertEquals(sourceRule, ref.rule)
            } else {
                assertEquals(sinkStatement, ref.statement)
                assertEquals(sinkRule, ref.rule)
            }
        }
    }

    @Test
    fun `a pass-through residual without a positive literal is not recorded`() {
        val recorder = MarkSetRecorder()
        recorder.active = true
        val method = FakeMethod("m")
        val rule = FakeRule()

        recorder.recordSite(inst(method, 0), rule, SiteKind.PASS_THROUGH, RuleConditionRewriter.trueExpr, emptyList())
        recorder.recordSite(inst(method, 1), rule, SiteKind.PASS_THROUGH, literal("A", position(0), negated = true), emptyList())
        recorder.recordSite(inst(method, 2), rule, SiteKind.PASS_THROUGH, literal("B", position(0)), emptyList())

        val input = recorder.seal(roots = emptyList())
        assertEquals(1, input.program.sites.size)
        assertEquals(listOf("B"), input.markNames)
    }

    @Test
    fun `release drops every recorded table and stops recording`() {
        val recorder = MarkSetRecorder()
        recorder.active = true
        val caller = FakeMethod("caller")
        val callee = FakeMethod("callee")
        val statement = inst(caller)

        recorder.recordEdge(caller, statement, callee)
        recorder.recordStatement(statement)
        recorder.recordSite(statement, FakeRule(), SiteKind.SINK, literal("A", position(0)), gens = emptyList())
        recorder.recordCleaner(statement, literal("A", position(0)))
        assertEquals(1, recorder.seal(roots = listOf(caller)).program.sites.size)

        recorder.release()
        assertFalse(recorder.active)

        recorder.recordSite(statement, FakeRule(), SiteKind.SINK, literal("B", position(0)), gens = emptyList())
        val input = recorder.seal(roots = listOf(caller))
        assertEquals(0, input.program.methodCount)
        assertEquals(0, input.program.sites.size)
        assertTrue(input.program.callees.isEmpty())
        assertTrue(input.markNames.isEmpty())
        assertTrue(input.coveredStatements.isEmpty())
        assertTrue(input.program.cleanerAtoms.isEmpty)
    }

    @Test
    fun `concurrent recording seals the same program as sequential recording`() {
        val workload = randomWorkload(Random(42))

        val sequential = MarkSetRecorder().also { recorder ->
            recorder.active = true
            workload.forEach { it(recorder) }
        }.seal(workload.roots)

        val threads = 8
        val concurrent = MarkSetRecorder().also { recorder ->
            recorder.active = true
            val pool = Executors.newFixedThreadPool(threads)
            val start = CountDownLatch(1)
            val done = (0 until threads).map { t ->
                // Every thread records every event (so each one is recorded concurrently many
                // times), each in its own order.
                val events = workload.shuffled(Random(t))
                pool.submit {
                    start.await()
                    events.forEach { it(recorder) }
                }
            }
            start.countDown()
            done.forEach { it.get() }
            pool.shutdown()
        }.seal(workload.roots)

        assertEquals(canonical(sequential), canonical(concurrent))
        assertTrue(sequential.program.sites.isNotEmpty())
    }

    private class Workload(val events: List<(MarkSetRecorder) -> Unit>, val roots: List<CommonMethod>) :
        List<(MarkSetRecorder) -> Unit> by events

    private fun randomWorkload(random: Random): Workload {
        val methods = (0 until 30).map { FakeMethod("m$it") }
        val statements = methods.flatMap { m -> (0 until 5).map { inst(m, it) } }
        val rules = (0 until 10).map { FakeRule() }
        val marks = listOf("A", "B", "C", "D")

        fun residual(): RuleConditionRewriter.ExprOrConstant {
            val parts = (0 until random.nextInt(0, 3)).map {
                literal(marks.random(random), position(random.nextInt(0, 2)), negated = random.nextInt(5) == 0)
            }
            return when (parts.size) {
                0 -> RuleConditionRewriter.trueExpr
                1 -> parts.single()
                else -> and(parts)
            }
        }

        val events = mutableListOf<(MarkSetRecorder) -> Unit>()
        repeat(200) {
            val caller = methods.random(random)
            val callee = methods.random(random)
            val call = statements.random(random)
            events += { it.recordEdge(caller, call, callee) }
        }
        repeat(2_000) {
            val statement = statements.random(random)
            val ruleIdx = random.nextInt(rules.size)
            val rule = rules[ruleIdx]
            // The kind and gens are properties of the rule, as in the engine.
            val kind = SiteKind.entries[ruleIdx % SiteKind.entries.size]
            val gens = if (kind == SiteKind.PASS_THROUGH) emptyList() else listOf(marks[ruleIdx % marks.size])
            val cond = residual()
            events += { it.recordStatement(statement) }
            events += { it.recordSite(statement, rule, kind, cond, gens) }
        }
        repeat(100) {
            val statement = statements.random(random)
            val cond = residual()
            events += { it.recordCleaner(statement, cond) }
        }
        return Workload(events, methods.take(3))
    }

    /** The sealed input with every dense id replaced by the object or name it stands for. */
    private fun canonical(input: MarkSetInput): Map<String, Any> {
        val p = input.program
        fun MarkCond.render(): String = when (this) {
            MarkCond.True -> "T"
            MarkCond.False -> "F"
            is MarkCond.Lit -> input.markNames[mark]
            is MarkCond.And -> args.joinToString(",", "and(", ")") { it.render() }
            is MarkCond.Or -> args.joinToString(",", "or(", ")") { it.render() }
        }
        val sites = p.sites.indices.map { i ->
            val site = p.sites[i]
            val ref = input.sites[i]
            listOf(
                ref.statement, ref.rule, input.methods[site.method], site.kind, site.cond.render(),
                site.cond.hasJoinedCube(), site.gens.map { input.markNames[it] }, ref.genMarks,
            )
        }
        return mapOf(
            "sites" to sites.groupingBy { it }.eachCount(),
            "edges" to p.callees.indices.flatMap { c -> p.callees[c].map { input.methods[c] to input.methods[it] } }
                .groupingBy { it }.eachCount(),
            "roots" to p.roots.map { input.methods[it] }.toSet(),
            "methods" to input.methods.toSet(),
            "marks" to input.markNames.toSet(),
            "cleanerAtoms" to p.cleanerAtoms.stream().toArray().map { input.markNames[it] }.toSet(),
            "covered" to input.coveredStatements,
        )
    }
}
