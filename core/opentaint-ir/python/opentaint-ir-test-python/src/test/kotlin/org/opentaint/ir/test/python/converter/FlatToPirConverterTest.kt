package org.opentaint.ir.test.python.converter

import org.junit.jupiter.api.Test
import org.opentaint.ir.api.python.PIRAssign
import org.opentaint.ir.api.python.PIRBindFunctionExpr
import org.opentaint.ir.api.python.PIRClass
import org.opentaint.ir.api.python.PIRDiagnostic
import org.opentaint.ir.api.python.PIRDiagnosticSeverity
import org.opentaint.ir.api.python.PIRLocalVar
import org.opentaint.ir.api.python.PIRPhysicalLocation
import org.opentaint.ir.impl.python.PIRModuleImpl
import org.opentaint.ir.impl.python.flat.FlatAnyType
import org.opentaint.ir.impl.python.flat.FlatBindFunction
import org.opentaint.ir.impl.python.flat.FlatBlock
import org.opentaint.ir.impl.python.flat.FlatCFG
import org.opentaint.ir.impl.python.flat.FlatClass
import org.opentaint.ir.impl.python.flat.FlatClassField
import org.opentaint.ir.impl.python.flat.FlatClassType
import org.opentaint.ir.impl.python.flat.FlatDecorator
import org.opentaint.ir.impl.python.flat.FlatFunctionIR
import org.opentaint.ir.impl.python.flat.FlatFunctionKind
import org.opentaint.ir.impl.python.flat.FlatGlobalNameRef
import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatModuleField
import org.opentaint.ir.impl.python.flat.FlatModuleIR
import org.opentaint.ir.impl.python.flat.FlatParamKind
import org.opentaint.ir.impl.python.flat.FlatParameter
import org.opentaint.ir.impl.python.flat.FlatReturn
import org.opentaint.ir.impl.python.flatToPir.FlatToPirConverter
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertSame
import kotlin.test.assertTrue

class FlatToPirConverterTest {

    private fun stubModuleInit(qualifiedName: String = "m.__module_init__") = FlatFunctionIR(
        name = "__module_init__",
        qualifiedName = qualifiedName,
        parentQualifiedName = null,
        kind = FlatFunctionKind.MODULE_INIT,
        cfg = FlatCFG.EMPTY,
        parameters = emptyList(),
        returnType = FlatAnyType,
        isAsync = false,
        isGenerator = false,
        decorators = emptyList(),
    )

    @Test
    fun `minimal module round-trip`() {
        val flat = FlatModuleIR(
            moduleName = "m",
            path = "m.py",
            functions = listOf(
                FlatFunctionIR(
                    name = "foo",
                    qualifiedName = "m.foo",
                    parentQualifiedName = null,
                    kind = FlatFunctionKind.TOP_LEVEL,
                    cfg = FlatCFG.EMPTY,
                    parameters = listOf(FlatParameter("x", FlatAnyType, FlatParamKind.POSITIONAL_OR_KEYWORD, false, null)),
                    returnType = FlatAnyType,
                    isAsync = false,
                    isGenerator = false,
                    decorators = emptyList(),
                ),
            ),
            moduleInit = FlatFunctionIR(
                name = "__module_init__",
                qualifiedName = "m.__module_init__",
                parentQualifiedName = null,
                kind = FlatFunctionKind.MODULE_INIT,
                cfg = FlatCFG.EMPTY,
                parameters = emptyList(),
                returnType = FlatAnyType,
                isAsync = false,
                isGenerator = false,
                decorators = emptyList(),
            ),
            classes = emptyList(),
            fields = listOf(FlatModuleField("x", FlatClassType("builtins.int"), true)),
            diagnostics = emptyList(),
        )

        val module = FlatToPirConverter(flat).convert()

        assertEquals("m", module.name)
        assertEquals("m.py", module.path)
        assertEquals(1, module.functions.size)
        assertEquals("foo", module.functions[0].name)
        assertEquals("__module_init__", module.moduleInit.name)
        assertEquals(1, module.fields.size)
        assertEquals("x", module.fields[0].name)
    }

    @Test
    fun `class with properties and enclosingClass`() {
        val flat = FlatModuleIR(
            moduleName = "m",
            path = "m.py",
            functions = emptyList(),
            moduleInit = stubModuleInit(),
            classes = listOf(
                FlatClass(
                    name = "Cls",
                    qualifiedName = "m.Cls",
                    baseClasses = emptyList(),
                    mro = emptyList(),
                    methods = listOf(
                        FlatFunctionIR(
                            name = "val",
                            qualifiedName = "m.Cls.val",
                            parentQualifiedName = null,
                            kind = FlatFunctionKind.METHOD,
                            cfg = FlatCFG.EMPTY,
                            parameters = listOf(FlatParameter("self", FlatAnyType, FlatParamKind.POSITIONAL_OR_KEYWORD, false, null)),
                            returnType = FlatAnyType,
                            isAsync = false,
                            isGenerator = false,
                            decorators = listOf(FlatDecorator("property", "builtins.property", emptyList())),
                        ),
                        FlatFunctionIR(
                            name = "do_stuff",
                            qualifiedName = "m.Cls.do_stuff",
                            parentQualifiedName = null,
                            kind = FlatFunctionKind.METHOD,
                            cfg = FlatCFG.EMPTY,
                            parameters = listOf(
                                FlatParameter("self", FlatAnyType, FlatParamKind.POSITIONAL_OR_KEYWORD, false, null),
                                FlatParameter("arg", FlatAnyType, FlatParamKind.POSITIONAL_OR_KEYWORD, false, null),
                            ),
                            returnType = FlatAnyType,
                            isAsync = false,
                            isGenerator = false,
                            decorators = emptyList(),
                        ),
                    ),
                    fields = listOf(FlatClassField("x", FlatClassType("builtins.int"), false)),
                    nestedClasses = emptyList(),
                    decorators = emptyList(),
                    isAbstract = false,
                    isDataclass = false,
                    isEnum = false,
                ),
            ),
            fields = emptyList(),
            diagnostics = emptyList(),
        )

        val module = FlatToPirConverter(flat).convert()

        assertEquals(1, module.classes.size)
        val cls = module.classes[0]
        assertEquals(2, cls.methods.size)
        assertEquals(1, cls.fields.size)
        assertEquals(1, cls.properties.size)
        assertNotNull(cls.properties[0].getter)
        assertTrue(cls.properties[0].getter!!.isProperty)
        for (method in cls.methods) {
            assertSame(cls, method.enclosingClass)
        }
        assertSame(module, cls.module)
        for (method in cls.methods) {
            assertSame(module, method.module)
        }
    }

    private fun accessor(name: String, params: List<String>, vararg decorators: FlatDecorator) =
        FlatFunctionIR(
            name = name,
            qualifiedName = "m.Cls.$name",
            parentQualifiedName = null,
            kind = FlatFunctionKind.METHOD,
            cfg = FlatCFG.EMPTY,
            parameters = params.map {
                FlatParameter(it, FlatAnyType, FlatParamKind.POSITIONAL_OR_KEYWORD, false, null)
            },
            returnType = FlatAnyType,
            isAsync = false,
            isGenerator = false,
            decorators = decorators.toList(),
        )

    private fun classWith(methods: List<FlatFunctionIR>): PIRClass {
        val flat = FlatModuleIR(
            moduleName = "m",
            path = "m.py",
            functions = emptyList(),
            moduleInit = stubModuleInit(),
            classes = listOf(
                FlatClass(
                    name = "Cls",
                    qualifiedName = "m.Cls",
                    baseClasses = emptyList(),
                    mro = emptyList(),
                    methods = methods,
                    fields = emptyList(),
                    nestedClasses = emptyList(),
                    decorators = emptyList(),
                    isAbstract = false,
                    isDataclass = false,
                    isEnum = false,
                ),
            ),
            fields = emptyList(),
            diagnostics = emptyList(),
        )
        return FlatToPirConverter(flat).convert().classes.single()
    }

    @Test
    fun `property accessors are matched by decorator`() {
        val property = FlatDecorator("property", "builtins.property", emptyList())
        val setter = FlatDecorator("setter", "m.Cls.x.setter", emptyList())
        val deleter = FlatDecorator("deleter", "m.Cls.x.deleter", emptyList())

        val cls = classWith(
            listOf(
                accessor("x", listOf("self"), property),
                accessor("x", listOf("self", "v"), setter),
                accessor("x", listOf("self"), deleter),
            ),
        )

        val prop = cls.properties.single()
        assertEquals("x", prop.name)
        assertEquals(1, prop.getter!!.parameters.size)
        assertEquals(2, prop.setter!!.parameters.size)
        assertNotNull(prop.deleter)
    }

    @Test
    fun `same-named method without an accessor decorator is not an accessor`() {
        val property = FlatDecorator("property", "builtins.property", emptyList())

        val cls = classWith(
            listOf(
                accessor("x", listOf("self"), property),
                accessor("x", listOf("self")),
                accessor("x", listOf("self", "extra")),
            ),
        )

        val prop = cls.properties.single()
        assertNotNull(prop.getter)
        assertNull(prop.setter)
        assertNull(prop.deleter)
    }

    @Test
    fun `FlatBindFunction lowers to PIRAssign of PIRBindFunctionExpr`() {
        val bind = FlatBindFunction(
            target = FlatLocal("x"),
            function = FlatGlobalNameRef("mod.inner\$local0"),
            physicalLocation = PIRPhysicalLocation(
                lineStart = 7u, lineEnd = 7u, colStart = 0u, colEnd = 0u,
            ),
        )
        val cfg = FlatCFG(
            blocks = listOf(FlatBlock(0, listOf(bind, FlatReturn(null)), emptyList())),
            entryBlock = 0,
            exitBlocks = listOf(0),
        )

        val flat = FlatModuleIR(
            moduleName = "mod",
            path = "mod.py",
            functions = listOf(
                FlatFunctionIR(
                    name = "outer",
                    qualifiedName = "mod.outer",
                    parentQualifiedName = null,
                    kind = FlatFunctionKind.TOP_LEVEL,
                    cfg = cfg,
                    parameters = emptyList(),
                    returnType = FlatAnyType,
                    isAsync = false,
                    isGenerator = false,
                    decorators = emptyList(),
                ),
            ),
            moduleInit = stubModuleInit("mod.__module_init__"),
            classes = emptyList(),
            fields = emptyList(),
            diagnostics = emptyList(),
        )

        val module = FlatToPirConverter(flat).convert()
        val outer = module.functions.first { it.name == "outer" }
        val firstInst = outer.cfg.instList.first()

        val assign = assertIs<PIRAssign>(firstInst, "FlatBindFunction must lower to PIRAssign")
        val target = assertIs<PIRLocalVar>(assign.target, "PIRAssign target must be PIRLocalVar")
        assertEquals("x", target.name)
        val bindExpr = assertIs<PIRBindFunctionExpr>(
            assign.expr,
            "PIRAssign expr must be PIRBindFunctionExpr",
        )
        assertEquals("mod.inner\$local0", bindExpr.function.qualifiedName)
    }

    @Test
    fun `diagnostics pass through`() {
        val flat = FlatModuleIR(
            moduleName = "m",
            path = "m.py",
            functions = emptyList(),
            moduleInit = stubModuleInit(),
            classes = emptyList(),
            fields = emptyList(),
            diagnostics = listOf(PIRDiagnostic(PIRDiagnosticSeverity.ERROR, "test error", "fn", "TestException")),
        )

        val module = FlatToPirConverter(flat).convert()

        assertEquals(1, module.diagnostics.size)
        assertEquals("test error", module.diagnostics[0].message)
        assertIs<PIRModuleImpl>(module)
    }
}
