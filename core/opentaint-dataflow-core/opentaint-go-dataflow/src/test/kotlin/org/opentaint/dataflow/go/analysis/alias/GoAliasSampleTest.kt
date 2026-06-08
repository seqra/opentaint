package org.opentaint.dataflow.go.analysis.alias

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.cfg.GoIRCallTarget
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.ir.go.inst.GoIRCall
import org.opentaint.ir.go.value.GoIRParameterValue
import org.opentaint.ir.go.value.GoIRRegister
import java.nio.file.Path
import kotlin.io.path.Path
import kotlin.io.path.readText
import kotlin.test.assertTrue
import kotlin.test.fail

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GoAliasSampleTest {
    private val client = GoIRClient()
    private val samplesDir: Path by lazy {
        Path(System.getProperty("GO_ALIAS_SAMPLES_DIR") ?: error("GO_ALIAS_SAMPLES_DIR not set"))
    }

    @AfterAll
    fun tearDown() = client.close()

    @TestFactory
    fun aliasSamples(): List<DynamicTest> {
        val program = client.buildFromDir(samplesDir, GoIRLoadConfig()).program
        val sources = samplesDir.toFile().listFiles { f -> f.extension == "go" }!!
            .associate { it.name to it.toPath().readText() }

        val functions = program.allFunctions().filter {
            it.pkg?.importPath == "util" && it.hasBody &&
                (it.name.startsWith("Positive_") || it.name.startsWith("Negative_"))
        }

        val tests = mutableListOf<DynamicTest>()
        for (fn in functions) {
            val source = sources.entries.firstOrNull { (_, text) -> text.contains("func ${fn.name}(") } ?: continue
            val parsed = AliasDirective.parseSource(source.value)
            val expectations = parsed.expectations.filter { sourceContainsFunctionAt(source.value, fn.name, it.sourceLine) }
            if (expectations.isEmpty()) continue
            tests.add(DynamicTest.dynamicTest("${source.key}:${fn.name}") {
                runFunction(fn, parsed.depth, expectations)
            })
        }
        return tests
    }

    private fun sourceContainsFunctionAt(source: String, funcName: String, directiveLine: Int): Boolean {
        val lines = source.lines()
        for (i in directiveLine downTo 0) {
            val t = lines[i].trim()
            if (t.startsWith("func ")) return t.startsWith("func $funcName(") || t.contains(" $funcName(")
        }
        return false
    }

    private fun runFunction(fn: GoIRFunction, depth: Int, expectations: List<AliasDirective.Expectation>) {
        val aa = GoLocalAliasAnalysis(fn, GoLocalAliasAnalysis.Params(interProcCallDepth = depth))
        val sinks = fn.body!!.instructions.filterIsInstance<GoIRCall>().filter {
            (it.call.target as? GoIRCallTarget.Function)?.function?.name == "aliasSink"
        }
        expectations.forEachIndexed { i, exp ->
            val sink = sinks.getOrNull(i) ?: fail("${fn.name}: no marker sink #$i for directive at line ${exp.sourceLine}")
            val queryBase = when (val arg = sink.call.args.firstOrNull()) {
                is GoIRRegister -> AccessPathBase.LocalVar(arg.index)
                is GoIRParameterValue -> AccessPathBase.Argument(arg.paramIndex)
                else -> fail("${fn.name}: sink #$i first arg is not a register or parameter")
            }
            val aliases = aa.computeAliasWithRef(queryBase, sink)
            for (p in exp.paths) {
                val present = aliases.any { matches(it, p) }
                if (p.negated) {
                    assertTrue(!present, "${fn.name}: expected ABSENT ${render(p)} but found it in $aliases")
                } else {
                    assertTrue(present, "${fn.name}: expected ${render(p)} not found in $aliases")
                }
            }
        }
    }

    private fun matches(actual: AliasApInfo, expected: AliasDirective.Path): Boolean {
        if (actual.base != expected.base) return false
        if (actual.accessors.size != expected.accessors.size) return false
        return actual.accessors.indices.all { i ->
            val a = actual.accessors[i]
            val e = expected.accessors[i]
            if (a is GoAliasAccessor.Field && e is GoAliasAccessor.Field) a.fieldName == e.fieldName else a == e
        }
    }

    private fun render(p: AliasDirective.Path): String =
        "${if (p.negated) "!" else ""}${p.base}${p.accessors}"
}
