package org.opentaint.ir.test.python.protoToFlat

import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.ir.impl.python.flat.FlatAssign
import org.opentaint.ir.impl.python.flat.FlatAwait
import org.opentaint.ir.impl.python.flat.FlatBinOp
import org.opentaint.ir.impl.python.flat.FlatBindFunction
import org.opentaint.ir.impl.python.flat.FlatBranch
import org.opentaint.ir.impl.python.flat.FlatBuildDict
import org.opentaint.ir.impl.python.flat.FlatBuildList
import org.opentaint.ir.impl.python.flat.FlatBuildSet
import org.opentaint.ir.impl.python.flat.FlatBuildSlice
import org.opentaint.ir.impl.python.flat.FlatBuildString
import org.opentaint.ir.impl.python.flat.FlatBuildTuple
import org.opentaint.ir.impl.python.flat.FlatCall
import org.opentaint.ir.impl.python.flat.FlatClass
import org.opentaint.ir.impl.python.flat.FlatCompare
import org.opentaint.ir.impl.python.flat.FlatDeleteAttr
import org.opentaint.ir.impl.python.flat.FlatDeleteLocal
import org.opentaint.ir.impl.python.flat.FlatDeleteSubscript
import org.opentaint.ir.impl.python.flat.FlatFunctionIR
import org.opentaint.ir.impl.python.flat.FlatGetIter
import org.opentaint.ir.impl.python.flat.FlatGlobalNameRef
import org.opentaint.ir.impl.python.flat.FlatReadName
import org.opentaint.ir.impl.python.flat.FlatInst
import org.opentaint.ir.impl.python.flat.FlatLoadAttr
import org.opentaint.ir.impl.python.flat.FlatLoadSubscript
import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatModuleIR
import org.opentaint.ir.impl.python.flat.FlatNextIter
import org.opentaint.ir.impl.python.flat.FlatRaise
import org.opentaint.ir.impl.python.flat.FlatReturn
import org.opentaint.ir.impl.python.flat.FlatStoreAttr
import org.opentaint.ir.impl.python.flat.FlatStoreGlobal
import org.opentaint.ir.impl.python.flat.FlatStoreSubscript
import org.opentaint.ir.impl.python.flat.FlatTypeCheck
import org.opentaint.ir.impl.python.flat.FlatUnaryOp
import org.opentaint.ir.impl.python.flat.FlatUnpack
import org.opentaint.ir.impl.python.flat.FlatValue
import org.opentaint.ir.impl.python.flat.FlatYield
import org.opentaint.ir.impl.python.flat.FlatYieldFrom
import kotlin.test.assertEquals
import kotlin.test.assertTrue

@Tag("tier2")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class MypyNameResolutionTest : RawFlatModuleTestBase() {

    private fun localReads(fn: FlatFunctionIR): Set<String> {
        val out = HashSet<String>()
        for (block in fn.cfg.blocks) {
            for (inst in block.instructions) {
                addLocalReads(inst, out)
            }
        }
        return out
    }

    private fun globalRefs(fn: FlatFunctionIR): Set<Pair<String, String>> {
        val out = HashSet<Pair<String, String>>()
        for (block in fn.cfg.blocks) {
            for (inst in block.instructions) {
                addGlobalRefs(inst, out)
            }
        }
        return out
    }

    private fun addLocalReads(inst: FlatInst, out: MutableSet<String>) {
        forEachOperand(inst) { v -> if (v is FlatLocal) out.add(v.name) }
    }

    private fun addGlobalRefs(inst: FlatInst, out: MutableSet<Pair<String, String>>) {
        if (inst is FlatReadName) {
            val ref = inst.ref
            if (ref is FlatGlobalNameRef) {
                val qn = ref.qualifiedName
                val dot = qn.lastIndexOf('.')
                if (dot >= 0) out.add(qn.substring(dot + 1) to qn.substring(0, dot))
                else out.add(qn to "")
            }
        }
    }

    private inline fun forEachOperand(inst: FlatInst, f: (FlatValue) -> Unit) {
        when (inst) {
            is FlatAssign -> f(inst.source)
            is FlatBinOp -> { f(inst.left); f(inst.right) }
            is FlatUnaryOp -> f(inst.operand)
            is FlatCompare -> { f(inst.left); f(inst.right) }
            is FlatLoadAttr -> f(inst.obj)
            is FlatStoreAttr -> { f(inst.obj); f(inst.value) }
            is FlatLoadSubscript -> { f(inst.obj); f(inst.index) }
            is FlatStoreSubscript -> { f(inst.obj); f(inst.index); f(inst.value) }
            is FlatStoreGlobal -> f(inst.value)
            is FlatCall -> { f(inst.callee); inst.args.forEach { f(it.value) } }
            is FlatBuildList -> inst.elements.forEach(f)
            is FlatBuildTuple -> inst.elements.forEach(f)
            is FlatBuildSet -> inst.elements.forEach(f)
            is FlatBuildDict -> { inst.keys.forEach(f); inst.values.forEach(f) }
            is FlatBuildSlice -> { inst.obj?.let(f); inst.lower?.let(f); inst.upper?.let(f); inst.step?.let(f) }
            is FlatBuildString -> inst.parts.forEach(f)
            is FlatGetIter -> f(inst.iterable)
            is FlatNextIter -> f(inst.iterator)
            is FlatBranch -> f(inst.condition)
            is FlatReturn -> inst.value?.let(f)
            is FlatRaise -> { inst.exception?.let(f); inst.cause?.let(f) }
            is FlatYield -> inst.value?.let(f)
            is FlatYieldFrom -> f(inst.iterable)
            is FlatAwait -> f(inst.awaitable)
            is FlatTypeCheck -> f(inst.value)
            is FlatUnpack -> f(inst.source)
            is FlatDeleteLocal -> f(inst.local)
            is FlatDeleteAttr -> f(inst.obj)
            is FlatDeleteSubscript -> { f(inst.obj); f(inst.index) }
            is FlatBindFunction -> Unit
            else -> Unit
        }
    }

    private fun allFunctions(module: FlatModuleIR): List<FlatFunctionIR> {
        fun classMethods(cls: FlatClass): List<FlatFunctionIR> =
            cls.methods + cls.nestedClasses.flatMap(::classMethods)
        return module.functions + module.moduleInit +
            module.classes.flatMap(::classMethods)
    }

    private fun fn(module: FlatModuleIR, qualifiedSuffix: String): FlatFunctionIR =
        allFunctions(module).first { it.qualifiedName.endsWith(qualifiedSuffix) }

    @Test
    fun `module-level global reads as FlatGlobalRef, not FlatLocal`() {
        val source = """
            x = 42

            def reader():
                return x
        """
        val mod = lowerSourceToFlat(source)
        val reader = fn(mod, ".reader")

        val locals = localReads(reader)
        val globals = globalRefs(reader)
        assertTrue(
            "x" !in locals,
            "'x' must resolve to a global, not a local. locals=$locals, globals=$globals",
        )
        assertTrue(
            globals.any { it.first == "x" },
            "'x' must appear in globalRefs. globals=$globals",
        )
    }

    @Test
    fun `enclosing-function local stays FlatLocal inside a nested def`() {
        val source = """
            def outer():
                value = 1
                def inner():
                        return value
                return inner
        """
        val mod = lowerSourceToFlat(source)
        val inner = fn(mod, ".outer\$inner")

        val locals = localReads(inner)
        val globals = globalRefs(inner)
        assertTrue(
            "value" in locals,
            "'value' is a genuine capture and must stay a local. locals=$locals, globals=$globals",
        )
    }

    @Test
    fun `module-level global stays FlatGlobalRef inside a nested def`() {
        val source = """
            CONST = 99

            def outer():
                def inner():
                    return CONST
                return inner
        """
        val mod = lowerSourceToFlat(source)
        val inner = fn(mod, ".outer\$inner")

        val locals = localReads(inner)
        val globals = globalRefs(inner)
        assertTrue(
            "CONST" !in locals,
            "'CONST' must resolve to a global even from a nested def. locals=$locals, globals=$globals",
        )
    }

    @Test
    fun `builtin resolves to FlatGlobalRef in module builtins`() {
        val source = """
            def f(x):
                return print(x)
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val globals = globalRefs(f)
        assertTrue(
            "print" !in locals,
            "'print' must resolve to a global. locals=$locals, globals=$globals",
        )
        assertEquals(
            setOf("print" to "builtins"),
            globals.filter { it.first == "print" }.toSet(),
            "'print' must resolve to module 'builtins'. globals=$globals",
        )
    }

    @Test
    fun `module-level global reads as FlatGlobalRef from a method`() {
        val source = """
            CONFIG = 1

            class A:
                def m(self):
                    return CONFIG
        """
        val mod = lowerSourceToFlat(source)
        val m = fn(mod, ".A.m")

        val locals = localReads(m)
        val globals = globalRefs(m)
        assertTrue(
            "CONFIG" !in locals,
            "'CONFIG' must resolve to a global from a method. locals=$locals, globals=$globals",
        )
    }

    @Test
    fun `sibling top-level function reads as FlatGlobalRef`() {
        val source = """
            def helper():
                return 1

            def caller():
                return helper()
        """
        val mod = lowerSourceToFlat(source)
        val caller = fn(mod, ".caller")

        val locals = localReads(caller)
        val globals = globalRefs(caller)
        assertTrue(
            "helper" !in locals,
            "'helper' must resolve to a global. locals=$locals, globals=$globals",
        )
    }

    @Test
    fun `imported module name reads as FlatGlobalRef`() {
        val source = """
            import os

            def f():
                return os.getcwd()
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val globals = globalRefs(f)
        assertTrue(
            "os" !in locals,
            "'os' must resolve to a global. locals=$locals, globals=$globals",
        )
    }

    @Test
    fun `top-level function reading a module global has no free names`() {
        val source = """
            x = 1
            def f():
                return x
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val params = f.parameters.map { it.name }.toSet()
        val owned = params + collectLocalDefs(f)
        val directFree = locals - owned - f.globalNames
        assertTrue(
            directFree.isEmpty(),
            "f() must have no free names; got directFree=$directFree, locals=$locals, globals=${globalRefs(f)}",
        )
    }

    @Test
    fun `method reading a module global has no free names`() {
        val source = """
            CONFIG = 1
            class A:
                def m(self):
                    return CONFIG
        """
        val mod = lowerSourceToFlat(source)
        val m = fn(mod, ".A.m")

        val locals = localReads(m)
        val params = m.parameters.map { it.name }.toSet()
        val owned = params + collectLocalDefs(m)
        val directFree = locals - owned - m.globalNames
        assertTrue(
            directFree.isEmpty(),
            "A.m must have no free names; got directFree=$directFree, locals=$locals, globals=${globalRefs(m)}",
        )
    }

    @Test
    fun `nested def separates a genuine capture from a module global`() {
        val source = """
            G = 100

            def outer():
                local_x = 1
                def inner():
                    return local_x + G
                return inner
        """
        val mod = lowerSourceToFlat(source)
        val inner = fn(mod, ".outer\$inner")

        val locals = localReads(inner)
        val globals = globalRefs(inner)
        assertEquals(
            setOf("local_x"),
            locals.filter { !it.startsWith("$") }.toSet(),
            "inner locals must be just {local_x}; G is a global. locals=$locals, globals=$globals",
        )
        assertTrue(
            globals.any { it.first == "G" },
            "'G' must appear in globals. globals=$globals",
        )
    }

    @Test
    fun `imported module stays FlatGlobalRef inside a nested def`() {
        val source = """
            import os

            def outer():
                def inner():
                    return os.getcwd()
                return inner
        """
        val mod = lowerSourceToFlat(source)
        val inner = fn(mod, ".outer\$inner")

        val locals = localReads(inner)
        val globals = globalRefs(inner)
        assertTrue(
            "os" !in locals,
            "If 'os' appears in inner's FlatLocal reads, mypy did NOT resolve the import. " +
                "OBSERVED locals=$locals, globals=$globals",
        )
    }

    private fun collectLocalDefs(fn: FlatFunctionIR): Set<String> {
        val out = HashSet<String>()
        for (block in fn.cfg.blocks) {
            for (inst in block.instructions) {
                fun add(v: FlatValue?) { if (v is FlatLocal) out.add(v.name) }
                when (inst) {
                    is FlatAssign -> add(inst.target)
                    is FlatBinOp -> add(inst.target)
                    is FlatUnaryOp -> add(inst.target)
                    is FlatCompare -> add(inst.target)
                    is FlatLoadAttr -> add(inst.target)
                    is FlatLoadSubscript -> add(inst.target)
                    is FlatReadName -> add(inst.target)
                    is FlatBuildList -> add(inst.target)
                    is FlatBuildTuple -> add(inst.target)
                    is FlatBuildSet -> add(inst.target)
                    is FlatBuildDict -> add(inst.target)
                    is FlatBuildSlice -> add(inst.target)
                    is FlatBuildString -> add(inst.target)
                    is FlatGetIter -> add(inst.target)
                    is FlatTypeCheck -> add(inst.target)
                    is FlatCall -> inst.target?.let(::add)
                    is FlatYield -> inst.target?.let(::add)
                    is FlatYieldFrom -> inst.target?.let(::add)
                    is FlatAwait -> inst.target?.let(::add)
                    is FlatNextIter -> add(inst.target)
                    is FlatUnpack -> inst.targets.forEach(::add)
                    is FlatBindFunction -> add(inst.target)
                    else -> Unit
                }
            }
        }
        return out
    }
}
