package org.opentaint.semgrep.pattern

import org.opentaint.dataflow.configuration.python.serialized.PythonPosition
import org.opentaint.dataflow.configuration.python.serialized.PythonPositionBase
import org.opentaint.dataflow.configuration.python.serialized.PythonTarget
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCleaner
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCondition
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonEntryPointSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonRule
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSink
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSource
import org.opentaint.semgrep.pattern.conversion.PythonLanguageStrategy
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class PythonRuleEmitTest {
    private fun emit(resource: String): List<SerializedPythonRule> {
        val yaml = javaClass.classLoader.getResource(resource)!!.readText()
        val loader = SemgrepRuleLoader(listOf(PythonLanguageStrategy()))
        loader.registerRuleSet(yaml, Path(resource), Path("."), SemgrepLoadTrace())
        val loaded = loader.loadRules()

        @Suppress("UNCHECKED_CAST")
        val rule = loaded.rulesWithMeta.first().first as TaintRuleFromSemgrep<SerializedPythonRule>
        return rule.taintRules.flatMap { it.rules }
    }

    private fun SerializedPythonRule.functionTarget(): String? = (target as? PythonTarget.Function)?.function

    private fun SerializedPythonRule.attributeTarget(): String? = (target as? PythonTarget.Attribute)?.attribute

    @Test fun `qualified source taints the call result`() {
        val source = emit("python-rules/source-sink.yaml")
            .filterIsInstance<SerializedPythonSource>()
            .single { it.functionTarget() == "os.environ.get" }

        assertTrue(source.taint.isNotEmpty(), "expected a taint action")
        assertTrue(source.taint.all { it.pos.base == PythonPositionBase.Result }, "source taints the result")
    }

    @Test fun `instance-call sink checks its tainted positions`() {
        // `$DB.execute($Q, ...)` carries taint on the receiver ($DB) and on the argument ($Q);
        // the emitter produces one mark-checking sink per taint-carrying position.
        val sinks = emit("python-rules/source-sink.yaml")
            .filterIsInstance<SerializedPythonSink>()
            .filter { it.functionTarget() == "execute" }

        assertTrue(sinks.isNotEmpty(), "expected execute sink(s)")
        assertTrue(sinks.all { it.condition != null }, "each sink carries a taint condition")

        val bases = sinks.flatMap { it.condition!!.markPositions() }.map { it.base }.toSet()
        assertTrue(PythonPositionBase.This in bases, "a sink checks the \$DB receiver (this)")
        assertTrue(bases.any { it is PythonPositionBase.Argument }, "a sink checks the \$Q argument")
    }

    @Test fun `sanitizer becomes a cleaner rule`() {
        val cleaner = emit("python-rules/sanitizer.yaml")
            .filterIsInstance<SerializedPythonCleaner>()
            .single { it.functionTarget() == "shlex.quote" }

        assertTrue(cleaner.cleans.isNotEmpty(), "cleaner removes taint from at least one position")
    }

    @Test fun `metavar method name becomes a qualified regex target`() {
        val source = emit("python-rules/metavar-method.yaml")
            .filterIsInstance<SerializedPythonSource>()
            .single()

        // `requests.$METHOD(...)`: concrete enclosing + unconstrained metavar name -> a single
        // regex matched against the qualified callee.
        assertEquals("""requests\..*""", source.functionTarget())
    }

    @Test fun `function-def source becomes an entry-point source`() {
        val entryPoint = emit("python-rules/entrypoint-def.yaml")
            .filterIsInstance<SerializedPythonEntryPointSource>()
            .single()

        assertEquals(".*", entryPoint.functionTarget())
        assertTrue(entryPoint.taint.isNotEmpty(), "entry-point taints at least one parameter position")
    }

    @Test fun `qualified attribute read becomes an attribute-fqn source`() {
        // `flask.request`: concrete receiver folds ahead of the synthetic name, so the unpacked
        // attribute target must keep the qualifier (`flask.request`), not collapse to `request`.
        val source = emit("python-rules/attribute-source.yaml")
            .filterIsInstance<SerializedPythonSource>()
            .single { it.attributeTarget() == "flask.request" }

        assertTrue(source.taint.isNotEmpty(), "expected a taint action")
        assertTrue(source.taint.all { it.pos.base == PythonPositionBase.Result }, "attribute read taints the result")
    }

    private fun SerializedPythonCondition.markPositions(): List<PythonPosition> = when (this) {
        is SerializedPythonCondition.ContainsMark -> listOf(pos)
        is SerializedPythonCondition.And -> allOf.flatMap { it.markPositions() }
        is SerializedPythonCondition.Or -> anyOf.flatMap { it.markPositions() }
        is SerializedPythonCondition.Not -> not.markPositions()
        is SerializedPythonCondition.NumberOfArgs,
        is SerializedPythonCondition.ConstantCmp,
        is SerializedPythonCondition.ConstantMatches -> emptyList()
    }
}
