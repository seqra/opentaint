package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.go.config.GoConfigLoader
import kotlin.test.Test
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

class GoConfigLoaderTest {

    @Test
    fun bundledConfigLoadsAndContainsExpectedEntries() {
        val config = assertNotNull(GoConfigLoader.getConfig(), "bundled go-config not on classpath")
        assertTrue(config.passThrough.isNotEmpty(), "expected at least one pass-through rule")

        // The bundled config ships propagators for common stdlib functions like
        // strings.Replace / bytes.NewBuffer etc. Verify a few package-level
        // (receiver:false) examples survive deserialization.
        val names = config.passThrough.map { (it.function as GoNameMatcher.Simple).name }.toSet()
        assertTrue("Replace" in names, "expected strings.Replace propagator, saw ${names.take(5)}")
        assertTrue("NewReader" in names, "expected bufio.NewReader propagator")
    }

    @Test
    fun containerListPushBackRuleSurvivesLoading() {
        val config = assertNotNull(GoConfigLoader.getConfig())
        val pushBack = config.passThrough.filter {
            (it.pkg as? GoNameMatcher.Simple)?.name?.contains("container/list.List") == true &&
            (it.function as? GoNameMatcher.Simple)?.name?.contains("PushBack") == true
        }
        assertTrue(pushBack.isNotEmpty(), "container/list PushBack rule dropped during loading")
        assertTrue(pushBack.all { it.copy.isNotEmpty() }, "PushBack copy actions were dropped")
    }
}
