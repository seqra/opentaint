package org.opentaint.dataflow.configuration.python.serialized

import com.charleskorn.kaml.Yaml
import kotlinx.serialization.decodeFromString
import kotlinx.serialization.encodeToString
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
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
        val configPath = System.getProperty("python.config.path")
            ?: error("python.config.path system property is required")
        val config = java.io.File(configPath).inputStream().use { loadSerializedPythonTaintConfig(it) }

        assertTrue(config.entryPoint.isNotEmpty())
        assertTrue(config.source.isNotEmpty())
        assertTrue(config.sink.isNotEmpty())
        assertTrue(config.passThrough.isNotEmpty())
        assertTrue(config.cleaner.isNotEmpty())

        // EntryPoint: `function: .*` regex + per-action `decoratedWith` scope.
        val flaskEntryPoint = config.entryPoint.single {
            (it.target as? PythonTarget.Function)?.function == ".*"
        }
        assertTrue(flaskEntryPoint.taint.any { action ->
            action.decoratedWith == "flask.Flask.route"
        })
        // class(flask.request) appears as a ClassRef position.
        assertTrue(flaskEntryPoint.taint.any { action ->
            (action.pos as? PythonPosition.BaseOnly)?.base is PythonPositionBase.ClassRef
        })

        val viewEntryPoint = config.entryPoint.single {
            (it.target as? PythonTarget.Function)?.function == "dispatch_request"
        }
        assertTrue(viewEntryPoint.taint.any { action ->
            action.baseClass == "flask.views.View"
        })

        // Source: Function vs Attribute target.
        assertTrue(config.source.any { (it.target as? PythonTarget.Function)?.function == "os.getenv" })
        assertTrue(config.source.any { (it.target as? PythonTarget.Attribute)?.attribute == "os.environ" })

        // Signature attaches to the function target (not the rule body).
        val parseArgs = config.source.single { src ->
            (src.target as? PythonTarget.Function)?.function == "argparse.ArgumentParser.parse_args"
        }
        val parseArgsFn = parseArgs.target as PythonTarget.Function
        assertNotNull(parseArgsFn.signature)
        assertEquals(emptyList(), parseArgsFn.signature.args)
        assertEquals("*", parseArgsFn.signature.`return`)

        // Sink: condition.anyOf + meta(cwe, note).
        val zipExtract = config.sink.single {
            (it.target as? PythonTarget.Function)?.function == "zipfile.ZipFile.extractall"
        }
        val cond = zipExtract.condition
        assertTrue(cond is SerializedPythonCondition.Or)
        assertTrue(cond.anyOf.all { it is SerializedPythonCondition.ContainsMark })
        assertEquals(listOf(22), zipExtract.meta?.cwe)
        assertEquals("path-injection", zipExtract.meta?.note)

        // Sink with list-form pos: kwarg(messages) + [*]
        val anthropicSinks = config.sink.filter {
            (it.target as? PythonTarget.Function)?.function == "Anthropic.messages.create"
        }
        val anyMessagesPath = anthropicSinks.any { sink ->
            (sink.condition as? SerializedPythonCondition.Or)
                ?.anyOf
                .orEmpty()
                .filterIsInstance<SerializedPythonCondition.ContainsMark>()
                .any { mark ->
                    val pos = mark.pos
                    pos is PythonPosition.WithModifiers
                        && (pos.base as? PythonPositionBase.KwArgument)?.name == "messages"
                        && pos.modifiers == listOf(PythonPositionModifier.ArrayElement)
                }
        }
        assertTrue(anyMessagesPath, "expected list-form pos with [*] modifier on Anthropic.messages.create sink")

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

        // Cleaner: `for:` is preserved.
        val cleaner = config.cleaner.first { it.`for` == "url-redirection" }
        assertTrue(cleaner.cleans.isNotEmpty())
    }
}
