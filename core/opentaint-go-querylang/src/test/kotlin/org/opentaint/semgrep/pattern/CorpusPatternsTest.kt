package org.opentaint.semgrep.pattern

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.opentaint.semgrep.go.pattern.SemgrepGoPattern
import org.opentaint.semgrep.go.pattern.SemgrepGoPatternParser
import org.opentaint.semgrep.go.pattern.SemgrepGoPatternParsingResult
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class CorpusPatternsTest {
    private val parser = SemgrepGoPatternParser()

    /**
     * Two corpus entries are HTML/template fragments, not Go source
     * (`<{{ ... }}` and `<script ...>`). A Go parser correctly rejects them,
     * so they are expected to fail parsing rather than yield an AST.
     */
    private val knownNonGo = setOf(
        "<{{ ... }} ... >",
        "<script ...> ... ... ... ... ... </script>",
    )

    private fun loadPatterns(): List<String> {
        val text = javaClass.classLoader.getResource("patterns/corpus.txt")
            ?.readText() ?: error("corpus.txt not found on classpath")
        val out = mutableListOf<String>()
        val regex = Regex("===PATTERN===\\s*\\n(.*?)\\n===END===", RegexOption.DOT_MATCHES_ALL)
        for (m in regex.findAll(text)) {
            out.add(m.groupValues[1])
        }
        return out
    }

    /**
     * Every Go corpus pattern must parse to a non-`Raw` AST. The two known
     * non-Go fragments must instead be rejected as a parse failure.
     */
    @TestFactory
    fun corpusPatterns(): List<DynamicTest> {
        val patterns = loadPatterns()
        return patterns.mapIndexed { idx, p ->
            DynamicTest.dynamicTest("pattern[$idx]: ${p.lineSequence().firstOrNull()?.take(60)}") {
                val result = parser.parseSemgrepGoPattern(p)
                if (p in knownNonGo) {
                    assertTrue(
                        result is SemgrepGoPatternParsingResult.FailedASTParsing,
                        "non-Go fragment should fail parsing, got: $result",
                    )
                } else {
                    assertTrue(result is SemgrepGoPatternParsingResult.Ok, "pattern did not parse: $result")
                    assertTrue(
                        result.pattern !is SemgrepGoPattern.Raw,
                        "pattern produced a Raw fallback AST",
                    )
                }
            }
        }
    }

    @Test
    fun corpusSuccessRate() {
        val patterns = loadPatterns()
        val total = patterns.size
        var ok = 0
        var okRawAst = 0
        val failures = mutableListOf<Pair<String, SemgrepGoPatternParsingResult>>()
        for (p in patterns) {
            when (val r = parser.parseSemgrepGoPattern(p)) {
                is SemgrepGoPatternParsingResult.Ok -> {
                    ok++
                    if (r.pattern is SemgrepGoPattern.Raw) okRawAst++
                }
                else -> failures.add(p to r)
            }
        }
        val failed = total - ok
        println("Corpus: total=$total ok=$ok rawAstFallback=$okRawAst failed=$failed")
        failures.forEach { (pat, res) ->
            println("  FAIL: <<<${pat.replace("\n", "\\n")}>>> -> $res")
        }
        assertEquals(0, okRawAst, "No corpus pattern may produce a Raw fallback AST")
        // Everything parses except the two non-Go HTML/template fragments.
        assertEquals(total - knownNonGo.size, ok, "Unexpected parse failures beyond the known non-Go fragments")
        assertEquals(knownNonGo, failures.map { it.first }.toSet(), "Only the known non-Go fragments may fail to parse")
    }
}
