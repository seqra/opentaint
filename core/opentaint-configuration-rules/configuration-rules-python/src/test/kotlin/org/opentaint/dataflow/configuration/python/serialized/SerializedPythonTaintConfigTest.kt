package org.opentaint.dataflow.configuration.python.serialized

import com.charleskorn.kaml.Yaml
import kotlinx.serialization.decodeFromString
import kotlinx.serialization.encodeToString
import org.opentaint.python.config.PythonConfigLoader
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class SerializedPythonTaintConfigTest {

    @Test
    fun `NumberOfArgs condition round-trips and dispatches on n`() {
        val yaml = Yaml.default

        // Round-trip the standalone predicate.
        val original: SerializedPythonCondition = SerializedPythonCondition.NumberOfArgs(2)
        val encoded = yaml.encodeToString(original)
        val decoded = yaml.decodeFromString<SerializedPythonCondition>(encoded)
        assertEquals(original, decoded)

        // The polymorphic serializer dispatches on the `n` key, including when nested.
        val nested = yaml.decodeFromString<SerializedPythonCondition>(
            """
            allOf:
              - n: 1
              - tainted: cmdi
                pos: arg(0)
            """.trimIndent()
        )
        assertTrue(nested is SerializedPythonCondition.And)
        val args = nested.allOf
        assertEquals(SerializedPythonCondition.NumberOfArgs(1), args[0])
        assertTrue(args[1] is SerializedPythonCondition.ContainsMark)
    }

    // Both mark predicates carry a mark name, so they can only be told apart by the key they
    // serialize under: `tainted` is checked first and would otherwise swallow every `taintedAny`.
    @Test
    fun `mark conditions round-trip without collapsing into each other`() {
        val yaml = Yaml.default
        val pos = PythonPosition.BaseOnly(PythonPositionBase.Argument(0))

        val onAny: SerializedPythonCondition = SerializedPythonCondition.ContainsMarkOnAnyAccessor("cmdi", pos)
        assertEquals(onAny, yaml.decodeFromString<SerializedPythonCondition>(yaml.encodeToString(onAny)))

        val plain: SerializedPythonCondition = SerializedPythonCondition.ContainsMark("cmdi", pos)
        assertEquals(plain, yaml.decodeFromString<SerializedPythonCondition>(yaml.encodeToString(plain)))
    }

    // The gate this diff moved off the action and into the condition: a structural predicate must
    // survive a round-trip and dispatch on its own key.
    @Test
    fun `structural conditions round-trip and dispatch on their own keys`() {
        val yaml = Yaml.default

        val decorated: SerializedPythonCondition = SerializedPythonCondition.MethodDecorated("flask.Flask.route")
        assertEquals(decorated, yaml.decodeFromString<SerializedPythonCondition>(yaml.encodeToString(decorated)))

        val extends: SerializedPythonCondition = SerializedPythonCondition.ClassExtends("flask.views.View")
        assertEquals(extends, yaml.decodeFromString<SerializedPythonCondition>(yaml.encodeToString(extends)))
    }

    @Test
    fun `constant conditions round-trip and dispatch on cmp and pattern`() {
        val yaml = Yaml.default

        val cmp: SerializedPythonCondition = SerializedPythonCondition.ConstantCmp(
            pos = PythonPosition.BaseOnly(PythonPositionBase.Argument(0)),
            value = SerializedPythonCondition.ConstantValue(SerializedPythonCondition.ConstantType.Str, "ok"),
            cmp = SerializedPythonCondition.ConstantCmpType.Eq,
        )
        assertEquals(cmp, yaml.decodeFromString<SerializedPythonCondition>(yaml.encodeToString(cmp)))

        val matches: SerializedPythonCondition = SerializedPythonCondition.ConstantMatches(
            pos = PythonPosition.BaseOnly(PythonPositionBase.Argument(0)),
            pattern = ".*",
        )
        assertEquals(matches, yaml.decodeFromString<SerializedPythonCondition>(yaml.encodeToString(matches)))

        // `not: { ... cmp: Eq }` must dispatch the inner node to ConstantCmp (via the `cmp` key).
        val negated = yaml.decodeFromString<SerializedPythonCondition>(yaml.encodeToString(SerializedPythonCondition.Not(cmp)))
        assertTrue(negated is SerializedPythonCondition.Not)
        assertTrue(negated.not is SerializedPythonCondition.ConstantCmp)
    }

    @Test
    fun `parses the shipped python config yaml end to end`() {
        val config = PythonConfigLoader.getConfig() ?: error("Couldn't load config")

        assertTrue(config.entryPoint.isEmpty())
        assertTrue(config.source.isEmpty())
        assertTrue(config.sink.isEmpty())
        assertTrue(config.cleaner.isEmpty())
        assertTrue(config.passThrough.isNotEmpty())

        // PassThrough: list-form `to:` and Attribute targets.
        val parseaddr = config.passThrough.single {
            (it.target as? PythonTarget.Function)?.function == "email.utils.parseaddr"
        }
        assertTrue(parseaddr.copy.any { it.to is PythonPosition.WithModifiers })
        assertTrue(config.passThrough.any {
            (it.target as? PythonTarget.Attribute)?.attribute == "flask.request.path"
        })

        // Field modifier `.filelist` parses.
        val zipFileCtor = config.passThrough.single {
            (it.target as? PythonTarget.Function)?.function == "zipfile.ZipFile"
        }
        val hasFieldModifier = zipFileCtor.copy.any { action ->
            (action.to as? PythonPosition.WithModifiers)
                ?.modifiers
                ?.any { it is PythonPositionModifier.Field && it.name == "filelist" } == true
        }
        assertTrue(hasFieldModifier, "expected `.filelist` field modifier on zipfile.ZipFile copy")
    }
}
