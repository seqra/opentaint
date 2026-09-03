package org.opentaint.ir.test.python.tier2

import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.*
import org.opentaint.ir.api.python.*
import org.opentaint.ir.impl.python.transforms.closure.ClosureRuntime
import org.opentaint.ir.test.python.PIRTestBase

@Tag("tier2")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ClosureNestedFunctionTest : PIRTestBase() {

    private lateinit var cp: PIRClasspath

    companion object {
        val SOURCE = """
def cnf_simple_nested(x):
    def inner(y):
        return y + 1
    return inner(x)

def cnf_closure_read():
    value = 10
    def reader():
        return value
    return reader()

def cnf_nonlocal_write():
    count = 0
    def increment():
        nonlocal count
        count = count + 1
    increment()
    increment()
    return count

def cnf_nonlocal_multiple():
    a = 1
    b = 2
    def swap():
        nonlocal a, b
        tmp = a
        a = b
        b = tmp
    swap()
    return a + b

def cnf_class_inside_func(val_arg):
    class LocalClass:
        def __init__(self, v):
            self.v = v
        def get(self):
            return self.v
    obj = LocalClass(val_arg)
    return obj.get()

def cnf_triple_nested(x):
    def middle(y):
        def deepest(z):
            return z * 2
        return deepest(y) + 1
    return middle(x)

def cnf_lambda_in_func(x):
    fn = lambda a: a + x
    return fn(10)

def cnf_lambda_in_nested(x):
    def wrapper(n):
        fn = lambda a: a + n
        return fn(10)
    return wrapper(x)

def cnf_closure_over_loop():
    funcs = []
    for i in range(5):
        def make(val_i=i):
            return val_i
        funcs.append(make)
    return funcs

def cnf_returns_inner():
    def factory():
        return 42
    return factory

def cnf_two_inner(x):
    def add_one(n):
        return n + 1
    def double(n):
        return n * 2
    return add_one(x) + double(x)

def cnf_inner_calls_inner(x):
    def helper(n):
        return n + 10
    def caller(n):
        return helper(n) * 2
    return caller(x)

def cnf_global_keyword():
    global MY_GLOBAL
    MY_GLOBAL = 100
    return MY_GLOBAL

MY_GLOBAL = 0

def cnf_deeply_nested():
    def level1():
        def level2():
            def level3():
                return 99
            return level3()
        return level2()
    return level1()

def cnf_decorator_inside():
    def my_decorator(func):
        def wrapper(*args):
            return func(*args)
        return wrapper
    @my_decorator
    def decorated(x):
        return x + 1
    return decorated(5)

def cnf_conditional_nested(flag):
    if flag:
        def helper():
            return 1
    else:
        def helper():
            return 2
    return helper()

def cnf_transitive(x):
    def cnf_transitive_mid():
        def cnf_transitive_inner():
            return x
        return cnf_transitive_inner()
    return cnf_transitive_mid()

def cnf_inv31_route(app):
    # Nested route referencing an undefined `e` (except has no `as e`) in a
    # never-run branch — a valid-but-buggy shape from the OWASP read_text
    # benchmark. `e` must not be mistaken for a capture (inv 31).
    def cnf_inv31_post():
        result = ""
        try:
            result = open("f").read()[:1000]
        except OSError:
            result = e.strerror
        return result
    return cnf_inv31_post
""".trimIndent()
    }

    @BeforeAll
    fun setup() {
        cp = buildFromSource(SOURCE)
    }

    @AfterAll
    fun teardown() {
        cp.close()
    }

    private fun findFunc(name: String): PIRFunction {
        for (m in cp.modules) {
            for (f in m.functions) {
                if (f.qualifiedName.endsWith(name)) return f
            }
            for (c in m.classes) {
                for (f in c.methods) {
                    if (f.qualifiedName.endsWith(name)) return f
                }
            }
        }
        throw AssertionError("Function not found: $name")
    }

    private fun findFuncOrNull(name: String): PIRFunction? {
        for (m in cp.modules) {
            for (f in m.functions) {
                if (f.qualifiedName.endsWith(name)) return f
            }
            for (c in m.classes) {
                for (f in c.methods) {
                    if (f.qualifiedName.endsWith(name)) return f
                }
            }
        }
        return null
    }

    private fun allInstructions(func: PIRFunction): List<PIRInstruction> =
        func.instList

    @Test
    fun `nested route with undefined name in except keeps its entry point (inv 31)`() {
        assertNotNull(
            findFuncOrNull("cnf_inv31_route\$cnf_inv31_post"),
            "nested route must remain a discoverable entry point, not a closure shim",
        )
        val shimmed = cp.modules.any { m ->
            (m.functions.map { it.name } + m.classes.map { it.name })
                .any { it.contains("<closure_") && it.contains("cnf_inv31") }
        }
        assertFalse(shimmed, "route must not be rewritten into a closure shim")
    }

    @Test
    fun `simple nested - outer has valid CFG`() {
        val f = findFunc("cnf_simple_nested")
        assertTrue(f.instList.isNotEmpty(), "cnf_simple_nested should have non-empty CFG")
    }

    @Test
    fun `simple nested - outer has call instruction`() {
        val calls = allInstructions(findFunc("cnf_simple_nested")).filterIsInstance<PIRCall>()
        assertTrue(calls.isNotEmpty(), "cnf_simple_nested should have PIRCall for inner(x)")
    }

    @Test
    fun `simple nested - outer has return instruction`() {
        val rets = allInstructions(findFunc("cnf_simple_nested")).filterIsInstance<PIRReturn>()
        assertTrue(rets.isNotEmpty(), "cnf_simple_nested should have PIRReturn")
    }

    @Test
    fun `closure read - outer has valid CFG`() {
        val f = findFunc("cnf_closure_read")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `closure read - outer has call and return`() {
        val insts = allInstructions(findFunc("cnf_closure_read"))
        assertTrue(insts.any { it is PIRCall }, "should call reader()")
        assertTrue(insts.any { it is PIRReturn }, "should return")
    }

    @Test
    fun `nonlocal write - outer has valid CFG`() {
        val f = findFunc("cnf_nonlocal_write")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `nonlocal write - outer has return`() {
        val rets = allInstructions(findFunc("cnf_nonlocal_write")).filterIsInstance<PIRReturn>()
        assertTrue(rets.isNotEmpty())
    }

    @Test
    fun `nonlocal write - outer has calls to increment`() {
        val calls = allInstructions(findFunc("cnf_nonlocal_write")).filterIsInstance<PIRCall>()
        assertTrue(calls.isNotEmpty(), "should call increment()")
    }

    @Test
    fun `nonlocal multiple - outer has valid CFG`() {
        val f = findFunc("cnf_nonlocal_multiple")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `class inside func - outer has valid CFG`() {
        val f = findFunc("cnf_class_inside_func")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `class inside func - outer has calls`() {
        val calls = allInstructions(findFunc("cnf_class_inside_func")).filterIsInstance<PIRCall>()
        assertTrue(calls.isNotEmpty(), "should call LocalClass() and obj.get()")
    }

    @Test
    fun `class inside func - outer has return`() {
        val rets = allInstructions(findFunc("cnf_class_inside_func")).filterIsInstance<PIRReturn>()
        assertTrue(rets.isNotEmpty())
    }

    @Test
    fun `triple nested - outer has valid CFG`() {
        val f = findFunc("cnf_triple_nested")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `triple nested - outer has call and return`() {
        val insts = allInstructions(findFunc("cnf_triple_nested"))
        assertTrue(insts.any { it is PIRCall })
        assertTrue(insts.any { it is PIRReturn })
    }

    @Test
    fun `lambda in func - lambda is extracted as synthetic function`() {
        val lambdas = cp.modules.flatMap { it.functions }
            .filter { it.qualifiedName.contains("<lambda>") }
        assertTrue(lambdas.isNotEmpty(), "Lambdas should be extracted at module level")
    }

    @Test
    fun `lambda in func - outer has valid CFG`() {
        val f = findFunc("cnf_lambda_in_func")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `lambda in func - outer has call and return`() {
        val insts = allInstructions(findFunc("cnf_lambda_in_func"))
        assertTrue(insts.any { it is PIRCall })
        assertTrue(insts.any { it is PIRReturn })
    }

    @Test
    fun `lambda in nested - outer has valid CFG`() {
        val f = findFunc("cnf_lambda_in_nested")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `closure over loop - outer has valid CFG`() {
        val f = findFunc("cnf_closure_over_loop")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `closure over loop - outer has iteration`() {
        val insts = allInstructions(findFunc("cnf_closure_over_loop"))
        val hasIter = insts.any { it.isAssignOf<PIRIterExpr>() || it is PIRNextIter }
        assertTrue(hasIter, "should have for-loop iteration")
    }

    @Test
    fun `returns inner - outer has valid CFG with return`() {
        val f = findFunc("cnf_returns_inner")
        assertTrue(f.instList.isNotEmpty())
        assertTrue(allInstructions(f).any { it is PIRReturn })
    }

    @Test
    fun `two inner - outer has valid CFG`() {
        val f = findFunc("cnf_two_inner")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `two inner - outer has multiple calls`() {
        val calls = allInstructions(findFunc("cnf_two_inner")).filterIsInstance<PIRCall>()
        assertTrue(calls.size >= 2, "should call add_one() and double()")
    }

    @Test
    fun `inner calls inner - outer has valid CFG`() {
        val f = findFunc("cnf_inner_calls_inner")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `global keyword - function has valid CFG`() {
        val f = findFunc("cnf_global_keyword")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `global keyword - function has assign and return`() {
        val insts = allInstructions(findFunc("cnf_global_keyword"))
        assertTrue(insts.any { it is PIRReturn })
        val hasAssign = insts.any { it is PIRAssign }
        assertTrue(hasAssign, "should assign to MY_GLOBAL")
    }

    @Test
    fun `deeply nested - outer has valid CFG`() {
        val f = findFunc("cnf_deeply_nested")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `deeply nested - outer has call and return`() {
        val insts = allInstructions(findFunc("cnf_deeply_nested"))
        assertTrue(insts.any { it is PIRCall })
        assertTrue(insts.any { it is PIRReturn })
    }

    @Test
    fun `decorator inside - outer has valid CFG`() {
        val f = findFunc("cnf_decorator_inside")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `decorator inside - outer returns`() {
        assertTrue(allInstructions(findFunc("cnf_decorator_inside")).any { it is PIRReturn })
    }

    @Test
    fun `conditional nested - outer has valid CFG`() {
        val f = findFunc("cnf_conditional_nested")
        assertTrue(f.instList.isNotEmpty())
    }

    @Test
    fun `conditional nested - outer has branches`() {
        val insts = allInstructions(findFunc("cnf_conditional_nested"))
        assertTrue(insts.any { it is PIRBranch }, "should have branch for if/else")
    }

    @Test
    fun `closureVars property is accessible on all functions`() {
        for (m in cp.modules) {
            for (f in m.functions) {
                assertNotNull(f.closureVars, "${f.qualifiedName} closureVars should be non-null")
            }
        }
    }

    @Test
    fun `all outer functions have valid non-empty CFGs`() {
        val names = listOf(
            "cnf_simple_nested", "cnf_closure_read", "cnf_nonlocal_write",
            "cnf_nonlocal_multiple", "cnf_class_inside_func", "cnf_triple_nested",
            "cnf_lambda_in_func", "cnf_lambda_in_nested", "cnf_closure_over_loop",
            "cnf_returns_inner", "cnf_two_inner", "cnf_inner_calls_inner",
            "cnf_global_keyword", "cnf_deeply_nested", "cnf_decorator_inside",
            "cnf_conditional_nested"
        )
        for (name in names) {
            val f = findFunc(name)
            assertTrue(f.instList.isNotEmpty(), "$name should have non-empty CFG")
            assertTrue(allInstructions(f).any { it is PIRReturn },
                "$name should have at least one PIRReturn")
        }
    }

    private fun findNestedFunc(pattern: String): PIRFunction? {
        val flatPattern = pattern.replace('.', '$')
        val direct = cp.modules.flatMap { it.functions }
            .firstOrNull { it.qualifiedName.contains(flatPattern) || it.qualifiedName.contains(pattern) }
        if (direct != null) return direct
        val baseName = pattern.substringAfterLast('.')
        return cp.modules.flatMap { it.functions }.firstOrNull { fn ->
            val n = fn.name
            n.startsWith("<closure_") && n.contains("\$$baseName") && n.endsWith("_impl>")
        }
    }

    private fun findAllNestedFuncs(pattern: String): List<PIRFunction> =
        cp.modules.flatMap { it.functions }.filter { it.qualifiedName.contains(pattern) }

    @Test
    fun `nested function inner is extracted as PIRFunction`() {
        val inner = findNestedFunc("cnf_simple_nested.inner")
        assertNotNull(inner, "inner should be extracted as a module-level PIRFunction")
    }

    @Test
    fun `nested function reader is extracted as PIRFunction`() {
        val reader = findNestedFunc("cnf_closure_read.reader")
        assertNotNull(reader, "reader should be extracted as a module-level PIRFunction")
    }

    @Test
    fun `nested function factory is extracted as PIRFunction`() {
        val factory = findNestedFunc("cnf_returns_inner.factory")
        assertNotNull(factory, "factory should be extracted as a module-level PIRFunction")
    }

    @Test
    fun `extracted inner function has valid CFG with return`() {
        val inner = findNestedFunc("cnf_simple_nested.inner")!!
        assertTrue(inner.instList.isNotEmpty(), "inner should have non-empty CFG")
        val rets = inner.instList.filterIsInstance<PIRReturn>()
        assertTrue(rets.isNotEmpty(), "inner should have PIRReturn")
    }

    @Test
    fun `extracted reader function has valid CFG with return`() {
        val reader = findNestedFunc("cnf_closure_read.reader")!!
        assertTrue(reader.instList.isNotEmpty(), "reader should have non-empty CFG")
        val rets = reader.instList.filterIsInstance<PIRReturn>()
        assertTrue(rets.isNotEmpty(), "reader should have PIRReturn")
    }

    @Test
    fun `extracted factory function has valid CFG with return`() {
        val factory = findNestedFunc("cnf_returns_inner.factory")!!
        assertTrue(factory.instList.isNotEmpty(), "factory should have non-empty CFG")
        val rets = factory.instList.filterIsInstance<PIRReturn>()
        assertTrue(rets.isNotEmpty(), "factory should have PIRReturn")
    }

    @Test
    fun `closureVars contains value for reader that captures outer local`() {
        val reader = findNestedFunc("cnf_closure_read.reader")!!
        assertTrue(reader.closureVars.any { it.contains("value") },
            "reader closureVars should contain 'value', got: ${reader.closureVars}")
    }

    @Test
    fun `closureVars contains count for increment using nonlocal`() {
        val increment = findNestedFunc("cnf_nonlocal_write.increment")!!
        assertTrue(increment.closureVars.any { it.contains("count") },
            "increment closureVars should contain 'count', got: ${increment.closureVars}")
    }

    @Test
    fun `closureVars contains a and b for swap using nonlocal`() {
        val swap = findNestedFunc("cnf_nonlocal_multiple.swap")!!
        val vars = swap.closureVars
        assertTrue(vars.any { it.contains("a") }, "swap closureVars should contain 'a', got: $vars")
        assertTrue(vars.any { it.contains("b") }, "swap closureVars should contain 'b', got: $vars")
    }

    @Test
    fun `triple nested - middle is extracted as PIRFunction`() {
        val middle = findNestedFunc("cnf_triple_nested.middle")
        assertNotNull(middle, "middle should be extracted from cnf_triple_nested")
    }

    @Test
    fun `triple nested - deepest is extracted through double nesting`() {
        val deepest = findNestedFunc("deepest")
        assertNotNull(deepest, "deepest should be extracted even through double nesting")
    }

    @Test
    fun `four-level nesting - level1 level2 level3 all extracted`() {
        val level1 = findNestedFunc("cnf_deeply_nested.level1")
        val level2 = findNestedFunc("level2")
        val level3 = findNestedFunc("level3")
        assertNotNull(level1, "level1 should be extracted")
        assertNotNull(level2, "level2 should be extracted")
        assertNotNull(level3, "level3 should be extracted")
    }

    @Test
    fun `inner qualifiedName contains enclosing function cnf_simple_nested`() {
        val inner = findNestedFunc("cnf_simple_nested.inner")!!
        assertTrue(inner.qualifiedName.contains("cnf_simple_nested"),
            "inner qualifiedName should contain 'cnf_simple_nested', got: ${inner.qualifiedName}")
    }

    @Test
    fun `deepest qualifiedName contains enclosing function middle`() {
        val deepest = findNestedFunc("deepest")!!
        assertTrue(deepest.qualifiedName.contains("middle"),
            "deepest qualifiedName should contain 'middle', got: ${deepest.qualifiedName}")
    }

    @Test
    fun `middle qualifiedName contains enclosing function cnf_triple_nested`() {
        val middle = findNestedFunc("cnf_triple_nested.middle")!!
        assertTrue(middle.qualifiedName.contains("cnf_triple_nested"),
            "middle qualifiedName should contain 'cnf_triple_nested', got: ${middle.qualifiedName}")
    }

    @Test
    fun `two inner from cnf_two_inner - add_one and double both extracted`() {
        val addOne = findNestedFunc("cnf_two_inner.add_one")
        val double = findNestedFunc("cnf_two_inner.double")
        assertNotNull(addOne, "add_one should be extracted from cnf_two_inner")
        assertNotNull(double, "double should be extracted from cnf_two_inner")
    }

    @Test
    fun `two inner from cnf_two_inner - both have valid CFGs with return`() {
        val addOne = findNestedFunc("cnf_two_inner.add_one")!!
        val double = findNestedFunc("cnf_two_inner.double")!!
        assertTrue(addOne.instList.isNotEmpty(), "add_one should have non-empty CFG")
        assertTrue(double.instList.isNotEmpty(), "double should have non-empty CFG")
        assertTrue(addOne.instList.any { it is PIRReturn },
            "add_one should have PIRReturn")
        assertTrue(double.instList.any { it is PIRReturn },
            "double should have PIRReturn")
    }

    @Test
    fun `two inner from cnf_inner_calls_inner - helper and caller both extracted`() {
        val helper = findNestedFunc("cnf_inner_calls_inner.helper")
        val caller = findNestedFunc("cnf_inner_calls_inner.caller")
        assertNotNull(helper, "helper should be extracted from cnf_inner_calls_inner")
        assertNotNull(caller, "caller should be extracted from cnf_inner_calls_inner")
    }

    @Test
    fun `closure over loop - make is extracted as PIRFunction`() {
        val make = findNestedFunc("cnf_closure_over_loop.make")
        assertNotNull(make, "make should be extracted from cnf_closure_over_loop")
    }

    @Test
    fun `closure over loop - make has val_i default parameter`() {
        val make = findNestedFunc("cnf_closure_over_loop.make")!!
        val paramNames = make.parameters.map { it.name }
        assertTrue(paramNames.any { it.contains("val_i") },
            "make should have val_i default parameter, got params: $paramNames")
    }

    @Test
    fun `nonlocal count - increment closureVars is non-empty`() {
        val increment = findNestedFunc("cnf_nonlocal_write.increment")!!
        assertTrue(increment.closureVars.isNotEmpty(),
            "increment should have non-empty closureVars due to 'nonlocal count'")
    }

    @Test
    fun `nonlocal a b - swap has at least two closureVars`() {
        val swap = findNestedFunc("cnf_nonlocal_multiple.swap")!!
        assertTrue(swap.closureVars.size >= 2,
            "swap should have at least 2 closureVars for 'a' and 'b', got: ${swap.closureVars}")
    }

    @Test
    fun `reader has self at parameter index 0`() {
        val reader = findNestedFunc("cnf_closure_read.reader")!!
        assertTrue(reader.parameters.isNotEmpty(),
            "reader should have at least the synthetic <self> parameter")
        assertEquals("<self>", reader.parameters[0].name,
            "reader.parameters[0] should be <self>, got params: ${reader.parameters.map { it.name }}")
    }

    @Test
    fun `simple non-capturing inner has NO self parameter`() {
        val inner = findNestedFunc("cnf_simple_nested.inner")!!
        val paramNames = inner.parameters.map { it.name }
        assertFalse(paramNames.contains("<self>"),
            "non-capturing inner should not have <self>, got params: $paramNames")
        assertTrue(inner.closureVars.isEmpty(),
            "non-capturing inner should have empty closureVars, got: ${inner.closureVars}")
    }

    @Test
    fun `reader prologue extracts cell value from self closure env`() {
        val reader = findNestedFunc("cnf_closure_read.reader")!!
        val insts = reader.instList

        val envLoad = insts.filterIsInstance<PIRLoadAttr>().firstOrNull { la ->
            val obj = la.obj
            obj is PIRParameterRef && obj.name == ClosureRuntime.SELF_PARAM_NAME &&
                la.attribute == ClosureRuntime.ENV_ATTR_NAME
        }
        assertNotNull(envLoad,
            "reader should have a PIRLoadAttr extracting ${ClosureRuntime.ENV_ATTR_NAME} " +
                "from ${ClosureRuntime.SELF_PARAM_NAME}; insts=$insts")

        val envLocalName = (envLoad!!.target as? PIRLocalVar)?.name
        assertNotNull(envLocalName, "envLoad target should be a PIRLocalVar")
        assertTrue(envLocalName!!.startsWith("\$env"),
            "env local name should start with \$env, got: $envLocalName")

        val cellAssign = insts.filterIsInstance<PIRAssign>().firstOrNull { a ->
            val tgt = a.target
            val expr = a.expr
            tgt is PIRLocalVar && tgt.name.startsWith("\$cell\$value") &&
                expr is PIRSubscriptExpr &&
                (expr.obj as? PIRLocalVar)?.name == envLocalName &&
                (expr.index as? PIRStrConst)?.value == "value"
        }
        assertNotNull(cellAssign,
            "reader should have a PIRAssign(\$cell\$value = \$env[\"value\"]); insts=$insts")
    }

    @Test
    fun `reader reads value through cell load`() {
        val reader = findNestedFunc("cnf_closure_read.reader")!!
        val cellLoad = reader.instList.filterIsInstance<PIRLoadAttr>().firstOrNull { la ->
            la.attribute == "value" &&
                (la.obj as? PIRLocalVar)?.name?.startsWith("\$cell\$value") == true
        }
        assertNotNull(cellLoad,
            "reader should have a PIRLoadAttr loading 'value' from a \$cell\$value local; " +
                "insts=${reader.instList}")
    }

    @Test
    fun `outer cnf_closure_read emits pir_cell call and adapter constructor at bind site`() {
        val outer = findFunc("cnf_closure_read")
        val insts = outer.instList

        val nameByLocal = insts
            .filterIsInstance<PIRAssign>()
            .mapNotNull { a ->
                val ref = (a.expr as? PIRReadNameExpr)?.ref as? PIRGlobalNameRef ?: return@mapNotNull null
                a.target.index to ref.qualifiedName
            }
            .toMap()
        fun calleeQn(call: PIRCall): String? {
            val callee = call.callee as? PIRLocalVar ?: return null
            return nameByLocal[callee.index]
        }

        val cellCtorCalls = insts.filterIsInstance<PIRCall>().filter { call ->
            calleeQn(call) == "builtins.${ClosureRuntime.CELL_CLASS_NAME}"
        }
        assertTrue(cellCtorCalls.isNotEmpty(),
            "outer should have at least one PIRCall to ${ClosureRuntime.CELL_CLASS_NAME}() " +
                "for owning value's cell")

        val adapterCtors = insts.filterIsInstance<PIRCall>().filter { call ->
            val qn = calleeQn(call) ?: return@filter false
            qn.substringAfterLast('.').let {
                it.startsWith("<closure_") && !it.endsWith("_impl>")
            }
        }
        assertTrue(adapterCtors.isNotEmpty(),
            "outer should have a PIRCall to the synthesized adapter class constructor")

        val dictAssigns = insts.filterIsInstance<PIRAssign>().filter { it.expr is PIRDictExpr }
        assertTrue(dictAssigns.isNotEmpty(),
            "outer should have at least one PIRAssign building the env dict (PIRDictExpr)")
    }

    @Test
    fun `increment writes count through cell store`() {
        val increment = findNestedFunc("cnf_nonlocal_write.increment")!!

        val cellStore = increment.instList.filterIsInstance<PIRStoreAttr>().firstOrNull { sa ->
            sa.attribute == "value" &&
                (sa.obj as? PIRLocalVar)?.name?.startsWith("\$cell\$count") == true
        }
        assertNotNull(cellStore,
            "increment should have a PIRStoreAttr writing 'value' on a \$cell\$count local; " +
                "insts=${increment.instList}")

        assertTrue(increment.closureVars.contains("count"),
            "increment.closureVars should contain 'count', got: ${increment.closureVars}")
    }

    @Test
    fun `transitive capture - cnf_transitive_mid has closureVars containing x`() {
        val mid = findNestedFunc("cnf_transitive.cnf_transitive_mid")
            ?: findNestedFunc("cnf_transitive_mid")
        assertNotNull(mid, "cnf_transitive_mid should be extracted as a PIRFunction")
        assertTrue(mid!!.closureVars.contains("x"),
            "cnf_transitive_mid should transitively capture 'x' from cnf_transitive; " +
                "got closureVars: ${mid.closureVars}")
    }

    @Test
    fun `call to capturing reader does NOT pass self argument`() {
        val outer = findFunc("cnf_closure_read")
        val readerCalls = outer.instList.filterIsInstance<PIRCall>().filter { call ->
            val resolved = call.resolvedCallee
            if (resolved != null && resolved.endsWith("reader")) return@filter true
            val callee = call.callee
            callee is PIRLocalVar && callee.name == "reader"
        }
        assertTrue(readerCalls.isNotEmpty(),
            "outer should have a PIRCall to reader; insts=${outer.instList}")
        for (call in readerCalls) {
            assertEquals(0, call.args.size,
                "call to reader must not have any args (no implicit <self>), got args: ${call.args}")
        }
    }
}
