package org.opentaint.semgrep.pattern

import org.opentaint.dataflow.configuration.python.serialized.PythonPosition
import org.opentaint.dataflow.configuration.python.serialized.PythonPositionBase
import org.opentaint.dataflow.configuration.python.serialized.PythonPositionModifier
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

    private fun emitAll(resource: String): List<SerializedPythonRule> {
        val yaml = javaClass.classLoader.getResource(resource)!!.readText()
        val loader = SemgrepRuleLoader(listOf(PythonLanguageStrategy()))
        loader.registerRuleSet(yaml, Path(resource), Path("."), SemgrepLoadTrace())
        return loader.loadRules().rulesWithMeta.flatMap {
            @Suppress("UNCHECKED_CAST")
            (it.first as TaintRuleFromSemgrep<SerializedPythonRule>).taintRules.flatMap { tr -> tr.rules }
        }
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

    @Test fun `subscript source taints the result element`() {
        // `source()[0]`: the subscript adds an element accessor onto the subscripted call's result,
        // so the source marks `Result[*]` rather than the whole result.
        val source = emit("python-rules/subscript-source.yaml")
            .filterIsInstance<SerializedPythonSource>()
            .single { it.functionTarget() == "source" }

        val positions = source.taint.map { it.pos }
        assertTrue(positions.isNotEmpty(), "expected a taint action")
        assertTrue(
            positions.all {
                it is PythonPosition.WithModifiers &&
                    it.base == PythonPositionBase.Result &&
                    it.modifiers == listOf(PythonPositionModifier.ArrayElement)
            },
            "subscript source taints Result[*], got $positions",
        )
    }

    @Test fun `subscript-assignment sink emits no sink (engine gap)`() {
        // Reproducer for the trustbound / CWE-501 engine gap: the session-write sink
        // `flask.session[k] = v` is a subscript-STORE. A structural rule whose final (sink) statement
        // is a subscript-assignment `sess[$A] = $V` cannot be lowered — transformAssignment rejects a
        // non-metavar (subscript) assignment target (Assignment_target_not_metavar), which collapses the
        // whole `patterns` block, so ZERO taint rules are emitted. (Even if it did lower, sinks fire only
        // at calls/attributes — PIRMethodSequentFlowFunction.handleStoreSubscript performs no sink check.)
        // When store-target sinks become expressible, this assertion flips (emit becomes non-empty) — the
        // signal to enable the @Disabled trustbound OWASP entries.
        val all = emitAll("python-rules/subscript-assign-sink.yaml")
        assertTrue(all.isEmpty(), "expected zero emitted rules (subscript-store sink unsupported), got ${all.size}")
    }

    @Test fun `subscript-assignment source binds the metavar to the result element`() {
        // `$A = source()[0] ... sink($A)`: the metavar assignment must NOT drop the subscript's
        // element modifier. The source binds `$A` to `Result[*]` (the element), exactly like the
        // bare taint-mode `source()[0]` form, so an intraprocedural element read / for-loop
        // iteration of the source result propagates the mark to the sink.
        val source = emit("python-rules/subscript-assign-source.yaml")
            .filterIsInstance<SerializedPythonSource>()
            .single { it.functionTarget() == "source" }

        val positions = source.taint.map { it.pos }
        assertTrue(positions.isNotEmpty(), "expected a taint action")
        assertTrue(
            positions.all {
                it is PythonPosition.WithModifiers &&
                    it.base == PythonPositionBase.Result &&
                    it.modifiers == listOf(PythonPositionModifier.ArrayElement)
            },
            "subscript-assignment source taints Result[*], got $positions",
        )
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

    // A taint-reachability sink is expanded to check every position generically (arg(*)/This), so the
    // keyword name only survives on a *condition* over that keyword. `run($CMD, shell=True)` keeps
    // `shell=True` as a constant compare, which must land on kwarg(shell), not the over-broad arg(*).
    @Test fun `constant keyword-arg condition serializes as a named position`() {
        val sink = emitAll("python-rules/kwarg-const.yaml")
            .filterIsInstance<SerializedPythonSink>()
            .first { it.functionTarget() == "run" }

        assertEquals(
            setOf(PythonPositionBase.KwArgument("shell")),
            sink.condition!!.constantCmpPositions().map { it.base }.toSet(),
            "shell=True lands on kwarg(shell), not arg(*)",
        )
    }

    @Test fun `each constant keyword-arg condition keeps its own name`() {
        val sink = emitAll("python-rules/kwarg-const.yaml")
            .filterIsInstance<SerializedPythonSink>()
            .first { it.functionTarget() == "mrun" }

        assertEquals(
            setOf(PythonPositionBase.KwArgument("shell"), PythonPositionBase.KwArgument("check")),
            sink.condition!!.constantCmpPositions().map { it.base }.toSet(),
            "each keyword condition keeps its name (guard exemption preserves multi-kwarg)",
        )
    }

    @Test fun `constant positional after ellipsis stays any-argument`() {
        val sink = emitAll("python-rules/kwarg-const.yaml")
            .filterIsInstance<SerializedPythonSink>()
            .first { it.functionTarget() == "prun" }

        assertEquals(
            setOf(PythonPositionBase.Argument(null)),
            sink.condition!!.constantCmpPositions().map { it.base }.toSet(),
            "a positional `*->i` classifier must not be mistaken for a kwarg name",
        )
    }

    // Structural (non-`mode: taint`) rules synthesize source/sink from a `patterns:` block and keep
    // concrete argument positions, so a keyword condition there must also decode to a named position.
    @Test fun `structural rule keyword condition serializes as a named position`() {
        val sink = emitAll("python-rules/kwarg-structural.yaml")
            .filterIsInstance<SerializedPythonSink>()
            .single { it.functionTarget() == "sink" }

        assertEquals(
            setOf(PythonPositionBase.KwArgument("mode")),
            sink.condition!!.constantCmpPositions().map { it.base }.toSet(),
            "structural mode=\"constant\" lands on kwarg(mode), not arg(*)",
        )
    }

    // A structural `pattern-not` synthesizes a cleaner (dead-edge). A keyword condition distinguishing
    // the not-pattern must decode to a named position in the cleaner's guard, else it over-cleans on arg(*).
    @Test fun `structural not-pattern cleaner keyword condition serializes as a named position`() {
        val cleaners = emitAll("python-rules/kwarg-not-cleaner.yaml")
            .filterIsInstance<SerializedPythonCleaner>()
            .filter { it.functionTarget() == "transform" }

        assertTrue(cleaners.isNotEmpty(), "expected a transform cleaner from pattern-not")
        assertEquals(
            setOf(PythonPositionBase.KwArgument("mode")),
            cleaners.flatMap { it.condition!!.constantCmpPositions() }.map { it.base }.toSet(),
            "the cleaner guard checks kwarg(mode)==\"safe\", not arg(*)",
        )
    }

    // The source-mark placement path is the shared TaintRuleStrategy (createAssignMark), distinct from
    // the sink-condition path — proves the keyword name survives both lowerings, not just conditions.
    @Test fun `focused keyword-arg source taints the named position`() {
        val source = emit("python-rules/kwarg-source.yaml")
            .filterIsInstance<SerializedPythonSource>()
            .single { it.functionTarget() == "handler" }

        assertEquals(
            listOf(PythonPositionBase.KwArgument("payload")),
            source.taint.map { it.pos.base },
            "a focused kwarg source marks kwarg(payload); without the fix this is arg(*) and crashes at runtime",
        )
    }

    private fun SerializedPythonCondition.constantCmpPositions(): List<PythonPosition> = when (this) {
        is SerializedPythonCondition.ConstantCmp -> listOf(pos)
        is SerializedPythonCondition.And -> allOf.flatMap { it.constantCmpPositions() }
        is SerializedPythonCondition.Or -> anyOf.flatMap { it.constantCmpPositions() }
        is SerializedPythonCondition.Not -> not.constantCmpPositions()
        is SerializedPythonCondition.ContainsMark,
        is SerializedPythonCondition.ContainsMarkOnAnyAccessor,
        is SerializedPythonCondition.NumberOfArgs,
        is SerializedPythonCondition.ConstantMatches -> emptyList()
    }

    private fun SerializedPythonCondition.markPositions(): List<PythonPosition> = when (this) {
        is SerializedPythonCondition.ContainsMark -> listOf(pos)
        is SerializedPythonCondition.ContainsMarkOnAnyAccessor -> listOf(pos)
        is SerializedPythonCondition.And -> allOf.flatMap { it.markPositions() }
        is SerializedPythonCondition.Or -> anyOf.flatMap { it.markPositions() }
        is SerializedPythonCondition.Not -> not.markPositions()
        is SerializedPythonCondition.NumberOfArgs,
        is SerializedPythonCondition.ConstantCmp,
        is SerializedPythonCondition.ConstantMatches -> emptyList()
        is SerializedPythonCondition.ContainsMarkOnAnyAccessor -> listOf(pos)
    }
}
