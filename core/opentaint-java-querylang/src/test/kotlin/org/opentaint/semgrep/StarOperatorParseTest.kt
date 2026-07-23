package org.opentaint.semgrep

import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.tree.ParseTree
import org.opentaint.semgrep.pattern.Metavar
import org.opentaint.semgrep.pattern.SemgrepJavaPattern
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.antlr.JavaLexer
import org.opentaint.semgrep.pattern.antlr.JavaParser
import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import org.opentaint.semgrep.pattern.errorEntries
import org.opentaint.semgrep.pattern.parseJavaSemgrepPattern
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class StarOperatorParseTest {
    private fun collect(p: SemgrepJavaPattern): List<SemgrepJavaPattern> =
        listOf(p) + p.children.flatMap { collect(it) }

    private fun metavars(pattern: String): List<Metavar> =
        collect(parseJavaSemgrepPattern(pattern)).filterIsInstance<Metavar>()

    private fun blockingErrors(ruleText: String): List<String> {
        val trace = SemgrepLoadTrace()
        val loader = SemgrepRuleLoader(listOf(JavaLanguageStrategy()))
        loader.registerRuleSet(ruleText, Path("repro.yaml"), Path("."), trace)
        loader.loadRules()
        return trace.errorEntries().map { "${it.severity}/${it.step}: ${it.message}" }
    }

    // Walks the raw ANTLR parse tree (the parser path the rule loader uses) and counts how many
    // starred-metavar alternatives ($*VAR) were recognized in expression position.
    private fun starredMetavarCount(pattern: String): Int {
        val lexer = JavaLexer(CharStreams.fromString(pattern))
        val parser = JavaParser(CommonTokenStream(lexer))
        val tree: ParseTree = parser.semgrepPattern()
        var count = 0
        fun walk(node: ParseTree) {
            if (node is JavaParser.PrimaryStarredMetavarContext) count++
            for (i in 0 until node.childCount) walk(node.getChild(i))
        }
        walk(tree)
        return count
    }

    @Test
    fun `starred metavar in call argument`() {
        val mvs = metavars("sink(\$*Y);")
        val y = mvs.single { it.name == "\$Y" }
        assertTrue(y.star, "expected \$*Y to be starred")
    }

    @Test
    fun `prefix star, not suffix, marks the metavar`() {
        // The star is a `$*` prefix bound into the metavar token. `$Y * z` stays multiplication,
        // and the retired suffix form `$Y*` is no longer a starred metavar.
        assertEquals(1, starredMetavarCount("sink(\$*Y);"), "\$*Y must be a star")
        assertEquals(0, starredMetavarCount("sink(\$Y * z);"), "\$Y * z must not be a star")
        assertEquals(0, starredMetavarCount("sink(\$Y*);"), "retired suffix \$Y* must not be a star")
    }

    @Test
    fun `starred formal parameter metavar`() {
        val mvs = metavars(
            "@\$ANNOTATION(...) \$RT \$M(..., \$TYPE \$*UNTRUSTED, ...) { ... }"
        )
        val u = mvs.single { it.name == "\$UNTRUSTED" }
        assertTrue(u.star, "expected formal-parameter \$*UNTRUSTED to be starred")
    }

    @Test
    fun `starred typed variable declaration`() {
        // F5: the starred `variableDeclaratorId` alternative in a TYPED declaration must load
        // (no parse exception) and the declared LHS metavar must carry star=true.
        val mvs = metavars("String \$*UNTRUSTED = \$REQ.getParameter(\"q\");")
        val u = mvs.single { it.name == "\$UNTRUSTED" }
        assertTrue(u.star, "expected typed-declaration \$*UNTRUSTED to be starred")
    }

    @Test
    fun `starred bare return value`() {
        val mvs = metavars("return \$*UNTRUSTED;")
        val u = mvs.single { it.name == "\$UNTRUSTED" }
        assertTrue(u.star)
    }

    @Test
    fun `star pattern loads without blocking errors and binds same name`() {
        // \$UNTRUSTED appears starred in the source and unstarred in the sink;
        // they must refer to the same metavariable and the rule must load cleanly.
        val rule = """
            rules:
              - id: star-bind-repro
                options: { lib: true }
                severity: NOTE
                message: x
                languages: [java]
                mode: taint
                pattern-sources:
                  - pattern: ${'$'}*UNTRUSTED = src();
                pattern-sinks:
                  - pattern: sink(${'$'}UNTRUSTED);
        """.trimIndent()
        val errors = blockingErrors(rule)
        assertTrue(errors.isEmpty(), "star rule failed to load:\n" + errors.joinToString("\n"))
    }
}
