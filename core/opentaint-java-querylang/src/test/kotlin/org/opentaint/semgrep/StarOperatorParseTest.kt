package org.opentaint.semgrep

import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.tree.ParseTree
import org.opentaint.semgrep.pattern.Metavar
import org.opentaint.semgrep.pattern.SemgrepJavaPattern
import org.opentaint.semgrep.pattern.antlr.JavaLexer
import org.opentaint.semgrep.pattern.antlr.JavaParser
import org.opentaint.semgrep.pattern.parseJavaSemgrepPattern
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class StarOperatorParseTest {
    private fun collect(p: SemgrepJavaPattern): List<SemgrepJavaPattern> =
        listOf(p) + p.children.flatMap { collect(it) }

    private fun metavars(pattern: String): List<Metavar> =
        collect(parseJavaSemgrepPattern(pattern)).filterIsInstance<Metavar>()

    // Walks the raw ANTLR parse tree (the parser path the rule loader uses) and counts how many
    // starred-metavar alternatives ($VAR*) were recognized in expression position.
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
        val mvs = metavars("sink(\$Y*);")
        val y = mvs.single { it.name == "\$Y" }
        assertTrue(y.star, "expected \$Y* to be starred")
    }

    @Test
    fun `whitespace separates multiplication from star`() {
        // \$Y * z is multiplication, NOT a starred metavar: the grammar must not recognize a
        // PrimaryStarredMetavar for the whitespace-separated case (while it does for the adjacent one).
        assertEquals(0, starredMetavarCount("sink(\$Y * z);"), "\$Y * z must not be a star")
        assertEquals(1, starredMetavarCount("sink(\$Y*);"), "\$Y* must be a star")
    }

    @Test
    fun `starred formal parameter metavar`() {
        val mvs = metavars(
            "@\$ANNOTATION(...) \$RT \$M(..., \$TYPE \$UNTRUSTED*, ...) { ... }"
        )
        val u = mvs.single { it.name == "\$UNTRUSTED" }
        assertTrue(u.star, "expected formal-parameter \$UNTRUSTED* to be starred")
    }

    @Test
    fun `starred bare return value`() {
        val mvs = metavars("return \$UNTRUSTED*;")
        val u = mvs.single { it.name == "\$UNTRUSTED" }
        assertTrue(u.star)
    }
}
