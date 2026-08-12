package org.opentaint.semgrep.pattern.diff.load

import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertTrue

class SemgrepRuleLoaderExtensionTest {
    @Test
    fun `extension observes accepted parsed normal rule without changing load result`() {
        val yaml = """
            rules:
              - id: simple
                severity: NOTE
                message: simple
                languages: [java]
                pattern: foo()
        """.trimIndent()
        val observed = mutableListOf<ParsedNormalRuleSnapshot>()
        val extension = object : SemgrepRuleLoaderExtension {
            override fun onNormalRuleParsed(rule: ParsedNormalRuleSnapshot) {
                observed += rule
            }
        }

        val baseline = load(yaml)
        val extended = load(yaml, extension)

        assertEquals(baseline.first.rulesWithMeta.map { it.second }, extended.first.rulesWithMeta.map { it.second })
        assertEquals(baseline.first.disabledRules, extended.first.disabledRules)
        assertEquals(1, observed.size)
        assertEquals("rules.yaml:simple", observed.single().descriptor.qualifiedRuleId)
        assertEquals("simple", observed.single().descriptor.shortRuleId)
        assertEquals(Path("rules.yaml"), observed.single().descriptor.relativePath)
        assertIs<org.opentaint.semgrep.pattern.SemgrepMatchingRule<*>>(observed.single().rule)
    }

    @Test
    fun `extension observes declared and resolved join items`() {
        val yaml = """
            rules:
              - id: source
                options: { lib: true }
                severity: NOTE
                message: source
                languages: [java]
                pattern: ${'$'}X = source()
              - id: sink
                options: { lib: true }
                severity: NOTE
                message: sink
                languages: [java]
                pattern: sink(${'$'}X)
              - id: joined
                severity: NOTE
                message: joined
                languages: [java]
                mode: join
                join:
                  refs:
                    - rule: source
                      as: source
                    - rule: sink
                      as: sink
                  on:
                    - 'source.${'$'}X -> sink.${'$'}X'
        """.trimIndent()
        val parsed = mutableListOf<ParsedJoinRuleSnapshot>()
        val resolved = mutableListOf<ResolvedJoinRuleSnapshot>()
        val extension = object : SemgrepRuleLoaderExtension {
            override fun onJoinRuleParsed(rule: ParsedJoinRuleSnapshot) {
                parsed += rule
            }

            override fun onJoinRuleResolved(rule: ResolvedJoinRuleSnapshot) {
                resolved += rule
            }
        }

        load(yaml, extension)

        assertEquals(listOf("source", "sink"), parsed.single().refs.map { it.`as` })
        assertEquals(setOf("source", "sink"), resolved.single().items.keys)
        assertEquals("rules.yaml:source", resolved.single().items.getValue("source").effectiveRuleId)
        assertEquals("rules.yaml:sink", resolved.single().items.getValue("sink").effectiveRuleId)
        assertTrue(resolved.single().operations.isNotEmpty())
    }

    @Test
    fun `stock collector exposes snapshots in qualified id order`() {
        val yaml = """
            rules:
              - id: z-rule
                severity: NOTE
                message: z
                languages: [java]
                pattern: z()
              - id: a-rule
                severity: NOTE
                message: a
                languages: [java]
                pattern: a()
        """.trimIndent()
        val collector = RuleDiffLoadCollector()

        load(yaml, collector)

        assertEquals(
            listOf("rules.yaml:a-rule", "rules.yaml:z-rule"),
            collector.normalRules.keys.toList(),
        )
        assertTrue(collector.joinRules.isEmpty())
        assertTrue(collector.overrides.isEmpty())
        assertTrue(collector.resolvedJoinRules.isEmpty())
    }

    @Test
    fun `stock collector records resolved override target and effective rule`() {
        val yaml = """
            rules:
              - id: base
                severity: NOTE
                message: base
                languages: [java]
                pattern: base()
              - id: replacement
                options: { overrides: base }
                severity: NOTE
                message: replacement
                languages: [java]
                pattern: replacement()
        """.trimIndent()
        val collector = RuleDiffLoadCollector()

        load(yaml, collector)

        val override = collector.overrides.getValue("rules.yaml:base")
        assertEquals("rules.yaml:replacement", override.overridingRule.qualifiedRuleId)
        assertEquals("rules.yaml:replacement", override.effectiveRuleId)
    }

    private fun load(
        yaml: String,
        extension: SemgrepRuleLoaderExtension? = null,
    ): Pair<SemgrepRuleLoader.RuleLoadResult, SemgrepLoadTrace> {
        val trace = SemgrepLoadTrace()
        val loader = SemgrepRuleLoader(
            listOf(JavaLanguageStrategy()),
            extension?.let(::listOf).orEmpty(),
        )
        loader.registerRuleSet(yaml, Path("rules.yaml"), Path("."), trace)
        return loader.loadRules() to trace
    }
}
