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
import org.opentaint.ir.impl.python.flat.FlatFunctionKind
import org.opentaint.ir.impl.python.flat.FlatGetIter
import org.opentaint.ir.impl.python.flat.FlatGlobalNameRef
import org.opentaint.ir.impl.python.flat.FlatInst
import org.opentaint.ir.impl.python.flat.FlatLoadAttr
import org.opentaint.ir.impl.python.flat.FlatLoadSubscript
import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatModuleIR
import org.opentaint.ir.impl.python.flat.FlatModuleNameRef
import org.opentaint.ir.impl.python.flat.FlatReadName
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
import org.opentaint.ir.impl.python.transforms.closure.FlatClosureTransformer
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

@Tag("tier2")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ImportNameResolutionTest : RawFlatModuleTestBase() {

    private fun localReads(fn: FlatFunctionIR): Set<String> {
        val out = HashSet<String>()
        for (block in fn.cfg.blocks) {
            for (inst in block.instructions) {
                forEachOperand(inst) { v -> if (v is FlatLocal) out.add(v.name) }
            }
        }
        return out
    }

    private fun globalRefs(fn: FlatFunctionIR): Set<Pair<String, String>> {
        val out = HashSet<Pair<String, String>>()
        for (block in fn.cfg.blocks) {
            for (inst in block.instructions) {
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
        }
        return out
    }

    private fun moduleRefs(fn: FlatFunctionIR): Set<String> {
        val out = HashSet<String>()
        for (block in fn.cfg.blocks) {
            for (inst in block.instructions) {
                if (inst is FlatReadName) {
                    val ref = inst.ref
                    if (ref is FlatModuleNameRef) out.add(ref.module)
                }
            }
        }
        return out
    }

    private fun importedAttrReads(fn: FlatFunctionIR): Set<Pair<String, String>> {
        val out = HashSet<Pair<String, String>>()
        for (block in fn.cfg.blocks) {
            val nameToModule = HashMap<String, String>()
            for (inst in block.instructions) {
                if (inst is FlatReadName) {
                    val ref = inst.ref
                    if (ref is FlatModuleNameRef) {
                        nameToModule[(inst.target as FlatLocal).name] = ref.module
                    }
                }
            }
            for (inst in block.instructions) {
                if (inst is FlatLoadAttr) {
                    val objName = (inst.obj as? FlatLocal)?.name
                    val mod = objName?.let(nameToModule::get)
                    if (mod != null) out.add(inst.attribute to mod)
                }
            }
        }
        return out
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
    fun `import os surfaces as FlatModuleRef in top-level function`() {
        val source = """
            import os

            def f():
                return os.getcwd()
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val modules = moduleRefs(f)
        val globals = globalRefs(f)
        assertFalse(
            "os" in locals,
            "'os' must not surface as FlatLocal. locals=$locals, modules=$modules",
        )
        assertTrue(
            "os" in modules,
            "expected FlatModuleRef(module=os). modules=$modules",
        )
        assertFalse(
            globals.any { it.first == "os" || it.second == "os" },
            "module name 'os' should not appear as a FlatGlobalRef. globals=$globals",
        )
    }

    @Test
    fun `from os import getcwd splits into ModuleRef plus LoadAttr`() {
        val source = """
            from os import getcwd

            def f():
                return getcwd()
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val globals = globalRefs(f)
        val modules = moduleRefs(f)
        val attrReads = importedAttrReads(f)
        assertFalse(
            "getcwd" in locals,
            "'getcwd' must not surface as FlatLocal. locals=$locals, attrReads=$attrReads",
        )
        assertTrue(
            "getcwd" to "os" in attrReads,
            "expected `LoadAttr(ModuleRef(os), getcwd)` for cross-module import; got attrReads=$attrReads",
        )
        assertTrue(
            "os" in modules,
            "expected the cross-module split to introduce a FlatModuleRef(os); got modules=$modules",
        )
        assertFalse(
            globals.any { it.first == "getcwd" && it.second == "os" },
            "cross-module `from os import getcwd` must NOT surface as FlatGlobalRef(os.getcwd); got globals=$globals",
        )
    }

    @Test
    fun `import alias for nested module chains through LoadAttr`() {
        val source = """
            import os.path as p

            def f():
                return p.join('a', 'b')
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val modules = moduleRefs(f)
        val attrReads = importedAttrReads(f)
        assertFalse(
            "p" in locals,
            "alias 'p' must not surface as FlatLocal. locals=$locals, modules=$modules",
        )
        assertTrue(
            "os" in modules,
            "alias 'p' should resolve to a chain rooted at FlatModuleRef(os); got modules=$modules",
        )
        assertFalse(
            "os.path" in modules,
            "FlatModuleRef must be single-segment; the dotted form 'os.path' must not appear. modules=$modules",
        )
        assertFalse(
            "p" in modules,
            "alias 'p' must be discarded — only the canonical root segment appears. modules=$modules",
        )
        assertTrue(
            "path" to "os" in attrReads,
            "alias 'p' must lower as `LoadAttr(ModuleRef(os), path)`; got attrReads=$attrReads",
        )
    }

    @Test
    fun `nested def reading imported module produces no spurious capture`() {
        val source = """
            import os

            def outer():
                def inner():
                    return os.getcwd()
                return inner
        """
        val mod = lowerSourceToFlat(source)
        val transformed = FlatClosureTransformer.transform(mod)

        val inner = fn(transformed, ".outer\$inner")
        val outer = fn(transformed, ".outer")

        assertEquals(
            emptySet(),
            inner.closureVars,
            "inner.closureVars should be empty after closure transform; got ${inner.closureVars}",
        )
        assertEquals(
            emptySet(),
            outer.closureVars,
            "outer.closureVars should be empty after closure transform; got ${outer.closureVars}",
        )
        assertTrue(
            inner.parameters.none { it.name == "<self>" },
            "inner must not gain a synthetic <self> parameter; got ${inner.parameters.map { it.name }}",
        )
        assertEquals(
            emptyList(),
            transformed.diagnostics.map { it.message },
            "no closure diagnostics expected for an import-only nested def",
        )
        assertTrue(
            "os" in moduleRefs(inner),
            "expected 'os' to appear as a FlatModuleRef in inner; got ${moduleRefs(inner)}",
        )
    }

    @Test
    fun `from import getcwd as alias resolves to canonical LoadAttr`() {
        val source = """
            from os import getcwd as g

            def f():
                return g()
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val globals = globalRefs(f)
        val attrReads = importedAttrReads(f)
        assertFalse(
            "g" in locals,
            "alias 'g' must not surface as FlatLocal. locals=$locals, attrReads=$attrReads",
        )
        assertTrue(
            "getcwd" to "os" in attrReads,
            "alias 'g' should resolve to `LoadAttr(ModuleRef(os), getcwd)` — the canonical name, " +
                "not the alias. attrReads=$attrReads",
        )
        assertFalse(
            attrReads.any { it.first == "g" },
            "alias 'g' should be discarded; only the canonical attribute 'getcwd' appears. attrReads=$attrReads",
        )
        assertFalse(
            globals.any { it.first == "getcwd" && it.second == "os" },
            "cross-module from-import must not surface as FlatGlobalRef(os.getcwd); got globals=$globals",
        )
    }

    // ─── Suppressed (unresolved) imports ───────────────────
    //
    // The rest of this file covers imports mypy can't resolve. For these
    // mypy creates a `Var(is_suppressed_import=True)` whose `_fullname` is
    // the *scope-prefixed bound name* (e.g. `__test__.helpers`), not the
    // canonical module / value path. The canonical target survives only on
    // the `Import` / `ImportFrom` statement nodes; the proto-to-Flat lowering
    // must consult those statements via CfgSession's import-scope maps.

    @Test
    fun `function-scoped suppressed import surfaces as FlatModuleRef`() {
        val source = """
            def f():
                import missing_pkg.sub
                return missing_pkg
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val modules = moduleRefs(f)
        assertFalse(
            "missing_pkg" in locals,
            "'missing_pkg' must not surface as FlatLocal. locals=$locals, modules=$modules",
        )
        assertTrue(
            "missing_pkg" in modules,
            "expected FlatModuleRef(missing_pkg) for function-scoped suppressed import. modules=$modules",
        )
    }

    @Test
    fun `module-level suppressed import surfaces as FlatModuleRef`() {
        val source = """
            import missing_pkg

            def f():
                return missing_pkg
        """
        val mod = lowerSourceToFlat(source)
        val modInit = fn(mod, ".__module_init__")
        val f = fn(mod, ".f")

        val fModules = moduleRefs(f)
        val fGlobals = globalRefs(f)
        assertTrue(
            "missing_pkg" in fModules,
            "expected FlatModuleRef(missing_pkg) at module-level suppressed import. fModules=$fModules, fGlobals=$fGlobals",
        )
        assertFalse(
            fGlobals.any { it.second == "__test__" && it.first == "missing_pkg" },
            "scope-prefixed FlatGlobalRef(__test__.missing_pkg) must NOT appear; got fGlobals=$fGlobals",
        )
        assertFalse(
            globalRefs(modInit).any { it.first == "missing_pkg" && it.second == "__test__" },
            "module-init must not emit FlatGlobalRef(__test__.missing_pkg)",
        )
    }

    @Test
    fun `suppressed import with alias chains through LoadAttr`() {
        val source = """
            def f():
                import missing_pkg.sub as alias
                return alias
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val modules = moduleRefs(f)
        val attrReads = importedAttrReads(f)
        assertFalse(
            "alias" in locals,
            "alias 'alias' must not surface as FlatLocal. locals=$locals",
        )
        assertTrue(
            "missing_pkg" in modules,
            "alias should resolve to a chain rooted at FlatModuleRef(missing_pkg). modules=$modules",
        )
        assertFalse(
            "missing_pkg.sub" in modules,
            "FlatModuleRef must be single-segment; the dotted form must not appear. modules=$modules",
        )
        assertTrue(
            "sub" to "missing_pkg" in attrReads,
            "alias should lower as `LoadAttr(ModuleRef(missing_pkg), sub)`; got attrReads=$attrReads",
        )
        assertFalse(
            "alias" in modules,
            "the alias name itself must not appear as a FlatModuleRef. modules=$modules",
        )
    }

    @Test
    fun `from suppressed module import value splits into ModuleRef plus LoadAttr`() {
        val source = """
            def f():
                from missing_pkg import value
                return value
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val attrReads = importedAttrReads(f)
        assertFalse(
            "value" in locals,
            "'value' must not surface as FlatLocal. locals=$locals, attrReads=$attrReads",
        )
        assertTrue(
            "value" to "missing_pkg" in attrReads,
            "expected `LoadAttr(ModuleRef(missing_pkg), value)` for suppressed `from`-import. attrReads=$attrReads",
        )
    }

    @Test
    fun `from suppressed module import value as alias resolves to canonical LoadAttr`() {
        val source = """
            def f():
                from missing_pkg import value as v
                return v
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val attrReads = importedAttrReads(f)
        assertFalse(
            "v" in locals,
            "alias 'v' must not surface as FlatLocal. locals=$locals, attrReads=$attrReads",
        )
        assertTrue(
            "value" to "missing_pkg" in attrReads,
            "alias 'v' should resolve to `LoadAttr(ModuleRef(missing_pkg), value)`. attrReads=$attrReads",
        )
        assertFalse(
            attrReads.any { it.first == "v" },
            "alias 'v' must be discarded; only canonical attribute 'value' appears. attrReads=$attrReads",
        )
    }

    @Test
    fun `from suppressed module import submodule defaults to LoadAttr`() {
        val source = """
            def f():
                from missing_pkg import submodule
                return submodule
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val attrReads = importedAttrReads(f)
        assertTrue(
            "submodule" to "missing_pkg" in attrReads,
            "without resolution we still produce `LoadAttr(ModuleRef(missing_pkg), submodule)`. attrReads=$attrReads",
        )
    }

    @Test
    fun `nested def reading function-scoped suppressed import is not a capture`() {
        val source = """
            def outer():
                import missing_pkg.sub
                def inner():
                    return missing_pkg
                return inner
        """
        val mod = lowerSourceToFlat(source)
        val transformed = FlatClosureTransformer.transform(mod)
        val outer = fn(transformed, ".outer")
        val inner = fn(transformed, ".outer\$inner")

        assertEquals(
            emptySet(),
            inner.closureVars,
            "inner must not capture 'missing_pkg' — it's an import, not a local. got ${inner.closureVars}",
        )
        assertEquals(
            emptySet(),
            outer.closureVars,
            "outer must remain capture-free. got ${outer.closureVars}",
        )
        assertTrue(
            "missing_pkg" in moduleRefs(inner),
            "inner should still emit a FlatModuleRef(missing_pkg). got ${moduleRefs(inner)}",
        )
    }

    @Test
    fun `function-scope import shadows module-level import of same name`() {
        val source = """
            import missing_pkg

            def f():
                from other_pkg import missing_pkg
                return missing_pkg
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val modules = moduleRefs(f)
        val attrReads = importedAttrReads(f)
        assertTrue(
            "missing_pkg" to "other_pkg" in attrReads,
            "function-scope `from other_pkg import missing_pkg` must shadow the module-level " +
                "`import missing_pkg` and emit `LoadAttr(ModuleRef(other_pkg), missing_pkg)`. " +
                "attrReads=$attrReads, modules=$modules",
        )
        assertFalse(
            "missing_pkg" in modules,
            "the shadowed module-level FlatModuleRef(missing_pkg) must NOT appear inside f. " +
                "Only FlatModuleRef(other_pkg) (the from-import owner) is expected. modules=$modules",
        )
    }

    @Test
    fun `same-scope import-then-from-import rebinds bound name to value`() {
        val source = """
            def f():
                import x
                from missing_pkg import x
                return x
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val modules = moduleRefs(f)
        val attrReads = importedAttrReads(f)
        assertTrue(
            "x" to "missing_pkg" in attrReads,
            "last write `from missing_pkg import x` should win and emit " +
                "`LoadAttr(ModuleRef(missing_pkg), x)`; got attrReads=$attrReads, modules=$modules",
        )
        assertFalse(
            "x" in modules,
            "the earlier `import x` binding must be replaced — only the from-import owner " +
                "FlatModuleRef(missing_pkg) is expected. modules=$modules",
        )
    }

    @Test
    fun `same-scope from-import-then-import rebinds bound name to module`() {
        val source = """
            def f():
                from missing_pkg import x
                import x
                return x
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val modules = moduleRefs(f)
        val globals = globalRefs(f)
        assertTrue(
            "x" in modules,
            "last write `import x` should win; got modules=$modules, globals=$globals",
        )
        assertFalse(
            globals.any { it.first == "x" && it.second == "missing_pkg" },
            "the earlier `from missing_pkg import x` binding must be replaced. globals=$globals",
        )
    }

    @Test
    fun `pre-import read falls back to FlatLocal, post-import read picks up canonical`() {
        val source = """
            def f():
                pre = missing_pkg
                import missing_pkg
                post = missing_pkg
                return (pre, post)
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val modules = moduleRefs(f)
        assertTrue(
            "missing_pkg" in locals,
            "the pre-import read should surface as FlatLocal (matches runtime " +
                "UnboundLocalError). locals=$locals, modules=$modules",
        )
        assertTrue(
            "missing_pkg" in modules,
            "the post-import read should surface as FlatModuleRef. " +
                "locals=$locals, modules=$modules",
        )
    }

    @Test
    fun `function-scoped suppressed import does not leak across functions`() {
        val source = """
            def has_import():
                import missing_pkg
                return missing_pkg

            def no_import(missing_pkg):
                return missing_pkg
        """
        val mod = lowerSourceToFlat(source)
        val hasImport = fn(mod, ".has_import")
        val noImport = fn(mod, ".no_import")

        assertTrue(
            "missing_pkg" in moduleRefs(hasImport),
            "the function with the import sees FlatModuleRef(missing_pkg)",
        )
        assertTrue(
            "missing_pkg" in localReads(noImport),
            "the sibling function's parameter must surface as FlatLocal; got locals=${localReads(noImport)}, modules=${moduleRefs(noImport)}",
        )
        assertFalse(
            "missing_pkg" in moduleRefs(noImport),
            "the sibling function must NOT pick up the other function's import map. modules=${moduleRefs(noImport)}",
        )
    }

    @Test
    fun `module-level lambda RHS sees textually-later import`() {
        val source = """
            config = lambda: missing_pkg.value
            import missing_pkg
        """
        val mod = lowerSourceToFlat(source)
        val lambda = allFunctions(mod).first { it.kind == FlatFunctionKind.LAMBDA }

        val modules = moduleRefs(lambda)
        val locals = localReads(lambda)
        val globals = globalRefs(lambda)
        assertTrue(
            "missing_pkg" in modules,
            "lambda body must see FlatModuleRef(missing_pkg) despite being lowered before " +
                "the textually-later import statement. modules=$modules, locals=$locals, globals=$globals",
        )
        assertFalse(
            "missing_pkg" in locals,
            "lambda body must not classify the import as a local. locals=$locals",
        )
        assertFalse(
            globals.any { it.first == "missing_pkg" && it.second == "__test__" },
            "lambda body must not emit a scope-prefixed FlatGlobalRef(__test__.missing_pkg). globals=$globals",
        )
    }

    @Test
    fun `bare builtin name stays as FlatGlobalRef`() {
        val source = """
            def f():
                return int
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val globals = globalRefs(f)
        val attrReads = importedAttrReads(f)
        assertTrue(
            "int" to "builtins" in globals,
            "bare builtin 'int' should surface as FlatGlobalRef(builtins.int). globals=$globals",
        )
        assertFalse(
            attrReads.any { it.second == "builtins" },
            "builtins are exempt — must not surface as `LoadAttr(ModuleRef(builtins), …)`. attrReads=$attrReads",
        )
    }

    @Test
    fun `set comprehension emits FlatGlobalRef for builtins set`() {
        val source = """
            def f(xs):
                return {x for x in xs}
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val globals = globalRefs(f)
        val attrReads = importedAttrReads(f)
        assertTrue(
            "set" to "builtins" in globals,
            "set comprehension's synthetic ref should be FlatGlobalRef(builtins.set); got globals=$globals",
        )
        assertFalse(
            attrReads.any { it.second == "builtins" },
            "synthetic builtins refs must not split into ModuleRef+LoadAttr. attrReads=$attrReads",
        )
    }

    @Test
    fun `same-module top-level reference stays as FlatGlobalRef`() {
        val source = """
            def helper():
                return 1

            def caller():
                return helper()
        """
        val mod = lowerSourceToFlat(source)
        val caller = fn(mod, ".caller")

        val globals = globalRefs(caller)
        val attrReads = importedAttrReads(caller)
        val modules = moduleRefs(caller)
        assertTrue(
            "helper" to "__test__" in globals,
            "same-module reference should be FlatGlobalRef(__test__.helper); got globals=$globals",
        )
        assertFalse(
            "__test__" in modules,
            "must not introduce a FlatModuleRef(__test__) for same-module refs. modules=$modules",
        )
        assertFalse(
            attrReads.any { it.second == "__test__" },
            "same-module refs must not split into `LoadAttr(ModuleRef(__test__), …)`. attrReads=$attrReads",
        )
    }

    @Test
    fun `from nested module import value chains through LoadAttr`() {
        val source = """
            from collections.abc import Iterable

            def f():
                return Iterable
        """
        val mod = lowerSourceToFlat(source)
        val f = fn(mod, ".f")

        val locals = localReads(f)
        val modules = moduleRefs(f)
        val attrReads = importedAttrReads(f)
        assertFalse(
            "Iterable" in locals,
            "'Iterable' must not surface as FlatLocal. locals=$locals, attrReads=$attrReads",
        )
        assertTrue(
            "collections" in modules,
            "expected the chain to root at FlatModuleRef(collections); got modules=$modules",
        )
        assertFalse(
            "collections.abc" in modules,
            "FlatModuleRef must be single-segment; the dotted form must not appear. modules=$modules",
        )
        assertTrue(
            "abc" to "collections" in attrReads,
            "expected `LoadAttr(ModuleRef(collections), abc)` as the first link in the chain; got attrReads=$attrReads",
        )
        val instructions = f.cfg.blocks.flatMap { it.instructions }
        val iterableLoad = instructions.filterIsInstance<FlatLoadAttr>().firstOrNull { it.attribute == "Iterable" }
        assertNotNull(iterableLoad, "expected a FlatLoadAttr reading `Iterable`; got $instructions")
        assertTrue(
            iterableLoad.obj is FlatLocal,
            "the `Iterable` LoadAttr's obj must be the FlatLocal temp returned by the previous LoadAttr; got ${iterableLoad.obj}",
        )
    }
}
