package org.opentaint.semgrep.pattern

import org.opentaint.semgrep.go.pattern.CallExpr
import org.opentaint.semgrep.go.pattern.ConcreteName
import org.opentaint.semgrep.go.pattern.DeepExpr
import org.opentaint.semgrep.go.pattern.Ellipsis
import org.opentaint.semgrep.go.pattern.EllipsisArgPrefix
import org.opentaint.semgrep.go.pattern.EllipsisStmt
import org.opentaint.semgrep.go.pattern.FuncDecl
import org.opentaint.semgrep.go.pattern.Identifier
import org.opentaint.semgrep.go.pattern.ImportDecl
import org.opentaint.semgrep.go.pattern.Metavar
import org.opentaint.semgrep.go.pattern.MetavarName
import org.opentaint.semgrep.go.pattern.SelectorExpr
import org.opentaint.semgrep.go.pattern.SemgrepGoPattern
import org.opentaint.semgrep.go.pattern.SemgrepGoPatternParser
import org.opentaint.semgrep.go.pattern.SemgrepGoPatternParsingResult
import org.opentaint.semgrep.go.pattern.StringEllipsis
import org.opentaint.semgrep.go.pattern.StringLiteral
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

class SemgrepGoPatternParserTest {
    private val parser = SemgrepGoPatternParser()

    private fun parse(pattern: String): SemgrepGoPattern {
        val r = parser.parseSemgrepGoPattern(pattern)
        assertTrue(r is SemgrepGoPatternParsingResult.Ok, "Expected Ok for `$pattern`, got $r")
        return r.pattern
    }

    /** Walks the AST and returns the first pattern matching the predicate, or null. */
    private fun find(p: SemgrepGoPattern, pred: (SemgrepGoPattern) -> Boolean): SemgrepGoPattern? {
        if (pred(p)) return p
        for (c in p.children) {
            find(c, pred)?.let { return it }
        }
        return null
    }

    @Test fun ellipsis() {
        val ast = parse("...")
        assertNotNull(find(ast) { it is EllipsisStmt || it is Ellipsis })
    }

    @Test fun callEllipsis() {
        val ast = parse("f(...)")
        val call = find(ast) { it is CallExpr } as? CallExpr
        assertNotNull(call)
        assertTrue(call.args is EllipsisArgPrefix)
    }

    @Test fun fmtPrintln() {
        val ast = parse("fmt.Println(\$X)")
        val call = find(ast) { it is CallExpr } as? CallExpr
        assertNotNull(call)
        val sel = call.fn as? SelectorExpr
        assertNotNull(sel)
        assertEquals(ConcreteName("Println"), sel.sel)
        // obj is fmt identifier
        val obj = sel.obj
        assertTrue(
            obj is Identifier && obj.name == ConcreteName("fmt"),
            "Expected obj to be Identifier(fmt), got $obj"
        )
        // Args contain $X metavar
        assertNotNull(find(call) { it is Metavar && it.name == "\$X" })
    }

    @Test fun deepEllipsis() {
        val ast = parse("<... \$X ...>")
        assertNotNull(find(ast) { it is DeepExpr })
    }

    @Test fun funcSig() {
        val ast = parse("func \$F(\$X int) int")
        val decl = find(ast) { it is FuncDecl } as? FuncDecl
        assertNotNull(decl)
        assertEquals(MetavarName("\$F"), decl.name)
    }

    @Test fun importStmt() {
        val ast = parse("import \"database/sql\"")
        assertNotNull(find(ast) { it is ImportDecl })
    }

    @Test fun metavarString() {
        val ast = parse("\"\$STR\"")
        val sl = find(ast) { it is StringLiteral && it.content is MetavarName } as? StringLiteral
        assertNotNull(sl)
        assertEquals(MetavarName("\$STR"), sl.content)
    }

    @Test fun ellipsisStringLit() {
        val ast = parse("\"...\"")
        assertNotNull(find(ast) { it is StringEllipsis })
    }

    @Test fun bareEllipsisParam() {
        val ast = parse("func f(...) {}")
        assertNotNull(find(ast) { it is FuncDecl })
    }

    @Test fun metavarEllipsisParam() {
        val ast = parse("func f(\$...ARGS) {}")
        assertNotNull(find(ast) { it is FuncDecl })
    }

    @Test fun structuralSmokeTest() {
        // 5 representative patterns -> AST non-Raw
        val patterns = listOf(
            "fmt.Println(\$X)",
            "\$X = \$Y + \$Z",
            "for ... { }",
            "&T{...}",
            "if \$X { return \$Y }",
        )
        for (p in patterns) {
            val ast = parse(p)
            assertTrue(ast !is SemgrepGoPattern.Raw, "Pattern `$p` produced Raw fallback")
        }
    }
}
