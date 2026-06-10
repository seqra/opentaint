package org.opentaint.dataflow.go.analysis.alias

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.cfg.GoIRCallTarget
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.ir.go.inst.GoIRCall
import org.opentaint.ir.go.value.GoIRRegister
import kotlin.io.path.createTempDirectory
import kotlin.io.path.writeText
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GoDSUAliasAnalysisTest {
    private val client = GoIRClient()

    @AfterAll
    fun tearDown() = client.close()

    private fun build(src: String): GoIRProgram {
        val dir = createTempDirectory("go-alias")
        dir.resolve("go.mod").writeText("module util\ngo 1.18\n")
        dir.resolve("s.go").writeText(src)
        return client.buildFromDir(dir, GoIRLoadConfig()).program
    }

    private fun GoIRProgram.func(name: String) = allFunctions().first { it.name == name }

    private fun sinkArgAliases(program: GoIRProgram, funcName: String, depth: Int = 0): List<AliasApInfo> {
        val fn = program.func(funcName)
        val aa = GoLocalAliasAnalysis(fn, GoLocalAliasAnalysis.Params(interProcCallDepth = depth))
        val sink = fn.body!!.instructions.filterIsInstance<GoIRCall>()
            .first { (it.call.target as? GoIRCallTarget.Function)?.function?.name == "aliasSink" }
        val arg = sink.call.args.first() as GoIRRegister
        return aa.computeAliasWithRef(AccessPathBase.LocalVar(arg.index), sink)
    }

    @Test
    fun `simple arg alias reaches sink`() {
        val program = build(
            """
            package util
            func aliasSink(x interface{}) {}
            func Positive_simple(a1, a2 interface{}, c bool) {
                var r interface{}
                if c { r = a1 } else { r = a2 }
                aliasSink(r)
            }
            """.trimIndent()
        )
        val aliases = sinkArgAliases(program, "Positive_simple")
        assertTrue(aliases.any { it.base == AccessPathBase.Argument(0) && it.accessors.isEmpty() }, "expected arg0, got $aliases")
        assertTrue(aliases.any { it.base == AccessPathBase.Argument(1) && it.accessors.isEmpty() }, "expected arg1, got $aliases")
    }

    @Test
    fun `direct call identity flows at depth 1`() {
        val program = build(
            """
            package util
            func aliasSink(x interface{}) {}
            func identity(x interface{}) interface{} { return x }
            func Positive_identity(src interface{}) {
                r := identity(src)
                aliasSink(r)
            }
            """.trimIndent()
        )
        val depth1 = sinkArgAliases(program, "Positive_identity", depth = 1)
        assertTrue(depth1.any { it.base == AccessPathBase.Argument(0) && it.accessors.isEmpty() }, "depth1 expected arg0, got $depth1")
        val depth0 = sinkArgAliases(program, "Positive_identity", depth = 0)
        assertTrue(depth0.none { it.base == AccessPathBase.Argument(0) }, "depth0 must NOT flow arg0 (external), got $depth0")
    }

    @Test
    fun `getter returns receiver field at depth 1`() {
        val program = build(
            """
            package util
            type Box struct{ value interface{} }
            func aliasSink(x interface{}) {}
            func get(b *Box) interface{} { return b.value }
            func Positive_getter(b *Box) {
                r := get(b)
                aliasSink(r)
            }
            """.trimIndent()
        )
        val aliases = sinkArgAliases(program, "Positive_getter", depth = 1)
        assertTrue(
            aliases.any { it.base == AccessPathBase.Argument(0) && it.accessors.size == 1 && it.accessors[0].let { a -> a is org.opentaint.dataflow.go.analysis.alias.GoAliasAccessor.Field && a.fieldName == "value" } },
            "expected arg0.value, got $aliases",
        )
    }

    @Test
    fun `closure captures free var at depth 1`() {
        val program = build(
            """
            package util
            func aliasSink(x interface{}) {}
            func Positive_closure(src interface{}) {
                f := func() interface{} { return src }
                r := f()
                aliasSink(r)
            }
            """.trimIndent()
        )
        val aliases = sinkArgAliases(program, "Positive_closure", depth = 1)
        assertTrue(aliases.any { it.base == AccessPathBase.Argument(0) && it.accessors.isEmpty() }, "expected captured arg0, got $aliases")
    }

    @Test
    fun `write then read field aliases src and field`() {
        val program = build(
            """
            package util
            type Box struct{ value interface{} }
            func aliasSink(x interface{}) {}
            func Positive_field(b *Box, src interface{}) {
                b.value = src
                dst := b.value
                aliasSink(dst)
            }
            """.trimIndent()
        )
        val aliases = sinkArgAliases(program, "Positive_field")
        assertTrue(aliases.any { it.base == AccessPathBase.Argument(1) && it.accessors.isEmpty() }, "expected arg1 (src), got $aliases")
    }
}
