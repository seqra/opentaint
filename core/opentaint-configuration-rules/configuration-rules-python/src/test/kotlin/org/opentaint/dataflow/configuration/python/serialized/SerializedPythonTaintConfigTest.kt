package org.opentaint.dataflow.configuration.python.serialized

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

class SerializedPythonTaintConfigTest {

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
        assertEquals(emptyList(), parseArgsFn.signature!!.args)
        assertEquals("*", parseArgsFn.signature!!.`return`)

        // Sink: condition.anyOf + meta(cwe, note).
        val zipExtract = config.sink.single {
            (it.target as? PythonTarget.Function)?.function == "zipfile.ZipFile.extractall"
        }
        val cond = zipExtract.condition
        assertTrue(cond is SerializedPythonCondition.Or)
        assertTrue((cond as SerializedPythonCondition.Or).anyOf.all { it is SerializedPythonCondition.ContainsMark })
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
        assertTrue(cleaner.cleans.all { it.taintKind != null })
    }
}
