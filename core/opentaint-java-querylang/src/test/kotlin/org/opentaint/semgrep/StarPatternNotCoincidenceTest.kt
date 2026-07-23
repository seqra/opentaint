package org.opentaint.semgrep

import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedItem
import org.opentaint.semgrep.pattern.SemgrepErrorEntry
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import org.opentaint.semgrep.pattern.createTaintConfig
import org.opentaint.semgrep.pattern.errorEntries
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * Rule-load diagnostic for the T/F cell of the star / pattern-not coincidence matrix:
 * a positive `$X*` (whole-object taint) coinciding at the SAME position with an unstarred
 * `pattern-not $X`. Its scoped 'keep field, drop base' semantics is unsupported; the combination
 * is treated as full (exclude-all) exclusion, same as the already-correct T/T case, and a non-fatal
 * diagnostic is surfaced through the rule-load trace.
 *
 * The rules mirror `untrusted-path-source.yaml` (a method-declaration source whose `pattern-not`
 * negates the same parameter position), because that is the shape whose coincidence is resolved in
 * `MethodConstraintsSolver.addNegative` — a call-argument `pattern-not` collapses at an earlier
 * automata-transform phase and never reaches the metavar solver.
 */
class StarPatternNotCoincidenceTest {
    private data class Loaded(
        val config: SerializedTaintConfig?,
        val errors: List<SemgrepErrorEntry>,
    )

    private fun load(ruleText: String): Loaded {
        val trace = SemgrepLoadTrace()
        val loader = SemgrepRuleLoader(listOf(JavaLanguageStrategy()))
        loader.registerRuleSet(ruleText, Path("star.yaml"), Path("."), trace)
        val ruleWithMeta = loader.loadRules().rulesWithMeta.singleOrNull()
        @Suppress("UNCHECKED_CAST")
        val config = (ruleWithMeta?.first as? TaintRuleFromSemgrep<SerializedItem>)?.createTaintConfig()
        return Loaded(config, trace.errorEntries())
    }

    private fun List<SemgrepErrorEntry>.coincidenceDiagnostics(): List<SemgrepErrorEntry> =
        filter {
            it.category == SemgrepErrorEntry.Category.UNSUPPORTED_FEATURE &&
                it.message.contains("whole-object taint occurrence")
        }

    /**
     * A method-declaration source whose `pattern-not` negates the same `$UNTRUSTED` parameter.
     * @param positiveStar  star on the positive `$UNTRUSTED` occurrence
     * @param notMetavar    the metavar spelled in the `pattern-not` param slot (with or without `*`)
     */
    private fun methodRule(id: String, positiveStar: Boolean, notMetavar: String): String {
        val pos = if (positiveStar) "${'$'}UNTRUSTED*" else "${'$'}UNTRUSTED"
        return """
            rules:
              - id: $id
                severity: NOTE
                message: x
                languages: [java]
                mode: taint
                pattern-sources:
                  - patterns:
                      - pattern: |
                          @${'$'}ANNOTATION(...)
                          ${'$'}RETURNTYPE ${'$'}METHODNAME(..., ${'$'}TYPE $pos,...) {
                            ...
                          }
                      - pattern-not: |
                          @${'$'}ANNOTATION(...)
                          ${'$'}RETURNTYPE ${'$'}METHODNAME(..., @PathVariable ${'$'}TYPE $notMetavar,...) {
                            ...
                          }
                pattern-sinks:
                  - pattern: sink(${'$'}S);
        """.trimIndent()
    }

    @Test
    fun `T-F coincidence emits a non-fatal diagnostic and still loads`() {
        val loaded = load(methodRule("cmp", positiveStar = true, notMetavar = "${'$'}UNTRUSTED"))
        val diagnostics = loaded.errors.coincidenceDiagnostics()
        assertTrue(
            diagnostics.isNotEmpty(),
            "expected a star/pattern-not coincidence diagnostic; got ${loaded.errors.map { it.message }}"
        )
        // Non-fatal: reported as NON_BLOCKING, and the rule STILL loads.
        assertTrue(
            diagnostics.all { it.severity == SemgrepErrorEntry.Severity.NON_BLOCKING },
            "diagnostic must be non-blocking; got ${diagnostics.map { it.severity }}"
        )
        assertTrue(loaded.config != null, "rule must still load despite the diagnostic")
    }

    @Test
    fun `T-F behaves as full exclusion, identical to the T-T case`() {
        // Same id so the two configs are byte-for-byte comparable (marks embed the rule id).
        val tf = load(methodRule("cmp", positiveStar = true, notMetavar = "${'$'}UNTRUSTED"))
        val tt = load(methodRule("cmp", positiveStar = true, notMetavar = "${'$'}UNTRUSTED*"))
        // T/T is the already-correct exclude-all case and must NOT emit the diagnostic.
        assertTrue(
            tt.errors.coincidenceDiagnostics().isEmpty(),
            "T/T (`pattern-not \$UNTRUSTED*`) must not emit the diagnostic; got ${tt.errors.map { it.message }}"
        )
        assertTrue(tf.config != null && tt.config != null, "both rules must load")
        // Same exclude-all behavior: the generated taint config is byte-for-byte identical.
        assertEquals(tt.config, tf.config, "T/F must produce the same (exclude-all) config as T/T")
    }

    @Test
    fun `structural non-coinciding pattern-not does not emit the diagnostic`() {
        // The pattern-not negates the same position with a DIFFERENT metavar (`$OTHER`) — a genuine
        // structural exclusion, not a coincidence with the positive `$UNTRUSTED*`.
        val loaded = load(methodRule("structural", positiveStar = true, notMetavar = "${'$'}OTHER"))
        assertTrue(
            loaded.errors.coincidenceDiagnostics().isEmpty(),
            "a non-coinciding structural pattern-not must not emit the diagnostic; got ${loaded.errors.map { it.message }}"
        )
    }

    @Test
    fun `starless F-F coincidence does not emit the diagnostic`() {
        // Positive is unstarred too: an exclude-all coincidence, but NOT the reserved combination.
        val loaded = load(methodRule("ff", positiveStar = false, notMetavar = "${'$'}UNTRUSTED"))
        assertTrue(
            loaded.errors.coincidenceDiagnostics().isEmpty(),
            "F/F (unstarred positive) must not emit the diagnostic; got ${loaded.errors.map { it.message }}"
        )
    }
}
