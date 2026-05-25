package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.go.rules.serialized.GoFunctionMatcher
import kotlin.test.Test
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

/**
 * Smoke test that the bundled `:go-config` JAR is on the classpath and parses
 * cleanly into a [org.opentaint.dataflow.go.rules.serialized.GoSerializedTaintConfig]. Detailed propagation behavior is
 * exercised in [org.opentaint.semgrep.GoSampleBasedTest] via the
 * `useDefaultConfig = true` opt-in.
 */
class GoConfigLoaderTest {

    @Test
    fun bundledConfigLoadsAndContainsExpectedEntries() {
        val config = assertNotNull(GoConfigLoader.getConfig(), "bundled go-config not on classpath")
        assertTrue(config.passThrough.isNotEmpty(), "expected at least one pass-through rule")

        // The bundled config ships propagators for common stdlib functions like
        // strings.Replace / bytes.NewBuffer etc. Verify a few package-level
        // (receiver:false) examples survive deserialization.
        val names = config.passThrough.map { (it.function as GoFunctionMatcher.Simple).name }.toSet()
        assertTrue("strings.Replace" in names, "expected strings.Replace propagator, saw ${names.take(5)}")
        assertTrue("bufio.NewReader" in names, "expected bufio.NewReader propagator")
    }
}
