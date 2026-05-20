package org.opentaint.dataflow.python.rules

import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.python.AllArguments
import org.opentaint.dataflow.configuration.python.ClassRef
import org.opentaint.dataflow.configuration.python.Condition
import org.opentaint.dataflow.configuration.python.Position
import org.opentaint.dataflow.configuration.python.PositionAccessor
import org.opentaint.dataflow.configuration.python.PositionWithAccess
import org.opentaint.dataflow.configuration.python.Target
import org.opentaint.dataflow.configuration.python.TypeMatcher
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class PIRTaintConfigurationTest {

    @Test
    fun `transforms the shipped python config into in-memory rules`() {
        val config = loadDefaultConfig()

        // Source: function target with mark interning.
        val getenv = config.sources.single { (it.target as? Target.Function)?.name == "os.getenv" }
        assertEquals("environment", getenv.taint.single().mark.name)
        assertEquals(Condition.ConstantTrue, getenv.condition)

        // Source: attribute target.
        assertTrue(config.sources.any { (it.target as? Target.Attribute)?.name == "os.environ" })

        // Signature lifted into Condition.SignatureMatches with `*` -> TypeMatcher.AnyType.
        val parseArgs = config.sources.single { (it.target as? Target.Function)?.name == "argparse.ArgumentParser.parse_args" }
        val sigCond = parseArgs.condition.firstSignatureMatch()
        assertEquals(emptyList(), sigCond.signature.args)
        assertEquals(TypeMatcher.AnyType, sigCond.signature.returnType)

        // Sink meta defaulting + id synthesis.
        val zipExtract = config.sinks.single {
            (it.target as? Target.Function)?.name == "zipfile.ZipFile.extractall"
        }
        assertEquals("function:zipfile.ZipFile.extractall", zipExtract.id)
        assertEquals(listOf(22), zipExtract.meta.cwe)
        assertEquals("path-injection", zipExtract.meta.note)
        assertEquals(CommonTaintConfigurationSinkMeta.Severity.Warning, zipExtract.meta.severity)

        // Sink condition: anyOf of ContainsMark — folded into Condition.Or / Condition.ContainsMark.
        val zipCond = zipExtract.condition
        assertTrue(zipCond is Condition.Or, "expected Or, got $zipCond")
        assertTrue((zipCond as Condition.Or).args.all { it is Condition.ContainsMark })

        // Entry point: `.*` rule split per (decoratedWith, baseClass) scope.
        // Original YAML has 4 actions across 2 decoratedWith values → 2 rules here.
        val flaskEntries = config.entryPoints.filter { (it.target as? Target.Function)?.name == ".*" }
        assertTrue(flaskEntries.size >= 2, "Flask entry rule should be split per scope, got ${flaskEntries.size}")
        val flaskRouteEntry = flaskEntries.single { entry ->
            entry.condition.containsScope(Condition.DecoratedWith("flask.Flask.route"))
        }
        // After lifting, actions are plain (mark, pos) pairs and AllArguments is a top-level Position.
        assertTrue(flaskRouteEntry.taint.any { it.pos === AllArguments })
        assertTrue(flaskRouteEntry.taint.any { it.pos is ClassRef })

        // baseClass entry-point (`dispatch_request`) lifts into Condition.BaseClass.
        val dispatch = config.entryPoints.first { (it.target as? Target.Function)?.name == "dispatch_request" }
        assertTrue(dispatch.condition.containsScope(Condition.BaseClass("flask.views.View")) ||
            dispatch.condition.containsScope(Condition.BaseClass("flask.views.MethodView")))

        // `.filelist` field accessor on a passThrough survives position conversion.
        val zipFileCtor = config.passThrough.single {
            (it.target as? Target.Function)?.name == "zipfile.ZipFile"
        }
        assertTrue(zipFileCtor.copy.any { action ->
            action.to.accessors().any { it is PositionAccessor.FieldAccessor && it.name == "filelist" }
        })

        // Cleaner: `for:` round-trips into forCategory.
        assertTrue(config.cleaners.any { it.forCategory == "url-redirection" })
    }

    /** True if [this] is exactly [c] or an [Condition.And] whose args contain [c]. */
    private fun Condition.containsScope(c: Condition): Boolean = when {
        this == c -> true
        this is Condition.And -> args.any { it == c }
        else -> false
    }

    /** Walks the [PositionWithAccess] chain and collects every accessor in path order. */
    private fun Position.accessors(): List<PositionAccessor> = when (this) {
        is PositionWithAccess -> base.accessors() + access
        else -> emptyList()
    }

    private fun Condition.firstSignatureMatch(): Condition.SignatureMatches = when (this) {
        is Condition.SignatureMatches -> this
        is Condition.And -> args.filterIsInstance<Condition.SignatureMatches>().single()
        else -> error("no SignatureMatches in $this")
    }
}
