package org.opentaint.dataflow.python.rules

import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.python.AllArguments
import org.opentaint.dataflow.configuration.python.ClassRef
import org.opentaint.dataflow.configuration.python.Result
import org.opentaint.dataflow.configuration.python.Target
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import org.opentaint.ir.api.python.PIRAnyType
import org.opentaint.ir.api.python.PIRClass
import org.opentaint.ir.api.python.PIRDecorator
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRParameter
import org.opentaint.ir.api.python.PIRType
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertSame
import kotlin.test.assertTrue

class PIRTaintConfigurationTest {

    @Test
    fun `source rule with FQN target resolves against matching method`() {
        val config = loadDefaultConfig()

        val getenv = stubMethod(qualifiedName = "os.getenv", shortName = "getenv")
        val sources = config.sourcesForMethod(getenv)

        assertEquals(1, sources.size)
        val source = sources.single()
        assertEquals(Target.Function(getenv), source.target)
        assertTrue(source.condition is CommonCondition.True)
        assertEquals("environment", source.taint.single().mark.name)
        assertEquals(Result, source.taint.single().pos)
    }

    @Test
    fun `unmatched FQN returns empty source list`() {
        val config = loadDefaultConfig()
        val other = stubMethod(qualifiedName = "some.unknown.func", shortName = "func")
        assertTrue(config.sourcesForMethod(other).isEmpty())
    }

    @Test
    fun `entry-point regex rule only fires for decorated methods`() {
        val config = loadDefaultConfig()

        val decorated = stubMethod(
            qualifiedName = "myapp.views.index",
            shortName = "index",
            decorators = listOf(stubDecorator("flask.Flask.route")),
        )
        val flaskEntries = config.entryPointSourcesForMethod(decorated)
        assertTrue(flaskEntries.isNotEmpty(), "expected flask.Flask.route entry-point to match")
        val first = flaskEntries.first()
        assertEquals(Target.Function(decorated), first.target)
        assertTrue(first.taint.any { it.pos === AllArguments })
        assertTrue(first.taint.any { it.pos is ClassRef })

        val bare = stubMethod(qualifiedName = "myapp.helpers.helper", shortName = "helper")
        assertTrue(config.entryPointSourcesForMethod(bare).isEmpty(),
            "regex rule must drop scope groups that don't apply")
    }

    @Test
    fun `entry-point base-class scope resolves against enclosing class MRO`() {
        val config = loadDefaultConfig()

        val viewCls = stubClass(
            qualifiedName = "myapp.MyView",
            baseClasses = listOf("flask.views.View"),
            mro = listOf("myapp.MyView", "flask.views.View", "object"),
        )
        val dispatch = stubMethod(
            qualifiedName = "myapp.MyView.dispatch_request",
            shortName = "dispatch_request",
            enclosingClass = viewCls,
        )
        assertTrue(config.entryPointSourcesForMethod(dispatch).isNotEmpty())

        val noBase = stubMethod(qualifiedName = "myapp.dispatch_request", shortName = "dispatch_request")
        assertTrue(config.entryPointSourcesForMethod(noBase).isEmpty(),
            "missing baseClass must drop the scope group")
    }

    @Test
    fun `sink defaulting + id synthesis`() {
        val config = loadDefaultConfig()
        val zipExtract = stubMethod(
            qualifiedName = "zipfile.ZipFile.extractall",
            shortName = "extractall",
        )
        val sinks = config.sinksForMethod(zipExtract)
        val sink = sinks.single()
        assertEquals("function:zipfile.ZipFile.extractall", sink.id)
        assertEquals(listOf(22), sink.meta.cwe)
        assertEquals("path-injection", sink.meta.note)
        assertEquals(CommonTaintConfigurationSinkMeta.Severity.Warning, sink.meta.severity)
        // anyOf folded into CommonCondition.Or of ContainsMark
        assertTrue(sink.condition is CommonCondition.Or)
        assertTrue((sink.condition as CommonCondition.Or).args.all { it is CommonCondition.Atom })
    }

    @Test
    fun `attribute source lookup is name-keyed`() {
        val config = loadDefaultConfig()
        val sources = config.sourcesForAttribute("os.environ")
        val source = sources.single()
        assertEquals(Target.Attribute("os.environ"), source.target)
        assertEquals("environment", source.taint.single().mark.name)
        assertTrue(config.sourcesForAttribute("not.an.attr").isEmpty())
    }

    @Test
    fun `signature match drops rule when arity differs`() {
        val config = loadDefaultConfig()

        val argParser = stubClass(
            qualifiedName = "argparse.ArgumentParser",
            baseClasses = emptyList(),
            mro = listOf("argparse.ArgumentParser", "object"),
        )
        // argparse.ArgumentParser.parse_args has signature `() *` — zero args after self.
        val matching = stubMethod(
            qualifiedName = "argparse.ArgumentParser.parse_args",
            shortName = "parse_args",
            parameters = listOf(stubParam("self", 0)),
            enclosingClass = argParser,
        )
        assertTrue(config.sourcesForMethod(matching).any { it.taint.single().mark.name == "commandargs" })

        val nonMatching = stubMethod(
            qualifiedName = "argparse.ArgumentParser.parse_args",
            shortName = "parse_args",
            parameters = listOf(stubParam("self", 0), stubParam("argv", 1)),
            enclosingClass = argParser,
        )
        assertTrue(config.sourcesForMethod(nonMatching).isEmpty(),
            "signature `() *` must reject arity > 0 after self")
    }

    @Test
    fun `per-method lookup result is cached`() {
        val config = loadDefaultConfig()
        val m = stubMethod(qualifiedName = "os.getenv", shortName = "getenv")
        val first = config.sourcesForMethod(m)
        val second = config.sourcesForMethod(m)
        assertSame(first, second, "lookup result must be cached identity-equal")
    }
}

// region Stubs

private fun stubMethod(
    qualifiedName: String,
    shortName: String,
    parameters: List<PIRParameter> = emptyList(),
    returnType: PIRType = PIRAnyType,
    decorators: List<PIRDecorator> = emptyList(),
    enclosingClass: PIRClass? = null,
): PIRFunction = object : PIRFunction {
    override val name: String = shortName
    override val qualifiedName: String = qualifiedName
    override val parameters: List<PIRParameter> = parameters
    override val returnType: PIRType = returnType
    override val decorators: List<PIRDecorator> = decorators
    override val enclosingClass: PIRClass? = enclosingClass
    override val cfg get() = error("not stubbed")
    override val instList get() = error("not stubbed")
    override val isAsync: Boolean get() = false
    override val isGenerator: Boolean get() = false
    override val isStaticMethod: Boolean get() = false
    override val isClassMethod: Boolean get() = false
    override val isProperty: Boolean get() = false
    override val closureVars: List<String> get() = emptyList()
    override val module get() = error("not stubbed")
    override fun flowGraph(): ControlFlowGraph<CommonInst> = error("not stubbed")
}

private fun stubClass(
    qualifiedName: String,
    baseClasses: List<String>,
    mro: List<String>,
): PIRClass = object : PIRClass {
    override val name: String = qualifiedName.substringAfterLast('.')
    override val qualifiedName: String = qualifiedName
    override val baseClasses: List<String> = baseClasses
    override val mro: List<String> = mro
    override val methods get() = error("not stubbed")
    override val fields get() = error("not stubbed")
    override val nestedClasses get() = error("not stubbed")
    override val properties get() = error("not stubbed")
    override val decorators get() = error("not stubbed")
    override val isAbstract: Boolean get() = false
    override val isDataclass: Boolean get() = false
    override val isEnum: Boolean get() = false
    override val module get() = error("not stubbed")
}

private fun stubDecorator(qualifiedName: String): PIRDecorator = object : PIRDecorator {
    override val name: String = qualifiedName.substringAfterLast('.')
    override val qualifiedName: String = qualifiedName
    override val arguments: List<String> = emptyList()
}

private fun stubParam(name: String, index: Int, type: PIRType = PIRAnyType): PIRParameter =
    object : PIRParameter {
        override val name: String = name
        override val type: PIRType = type
        override val kind get() = error("not stubbed")
        override val hasDefault: Boolean get() = false
        override val defaultValue get() = null
        override val index: Int = index
    }

// endregion
