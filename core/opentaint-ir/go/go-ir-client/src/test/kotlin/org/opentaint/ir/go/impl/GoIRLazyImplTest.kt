package org.opentaint.ir.go.impl

import org.assertj.core.api.Assertions.assertThat
import org.assertj.core.api.Assertions.assertThatThrownBy
import org.junit.jupiter.api.Test
import org.opentaint.ir.go.type.GoIRBasicType
import org.opentaint.ir.go.type.GoIRBasicTypeKind
import org.opentaint.ir.go.type.GoIRFuncType

class GoIRLazyImplTest {

    @Test
    fun `program creation with package placeholders does not load package declarations`() {
        var loadCount = 0
        val pkg = GoIRPackageImpl(
            importPath = "example.com/lazy",
            name = "lazy",
            loader = { loadCount++ },
        )
        val program = GoIRProgramImpl(mapOf(pkg.importPath to pkg))

        assertThat(program.packages).containsKey("example.com/lazy")
        assertThat(program.findPackage("example.com/lazy")).isSameAs(pkg)
        assertThat(loadCount).isZero()
    }

    @Test
    fun `package declarations load lazily and are cached`() {
        lateinit var pkg: GoIRPackageImpl
        var loadCount = 0
        pkg = GoIRPackageImpl(
            importPath = "example.com/lazy",
            name = "lazy",
            loader = {
                loadCount++
                pkg.addFunction(function("Declared"))
            },
        )

        assertThat(loadCount).isZero()
        assertThat(pkg.functions).extracting<String> { it.name }.containsExactly("Declared")
        assertThat(pkg.functions).extracting<String> { it.name }.containsExactly("Declared")
        assertThat(pkg.findFunction("Declared")).isNotNull
        assertThat(loadCount).isEqualTo(1)
    }

    @Test
    fun `package loaded flag is published only after loader completes`() {
        lateinit var pkg: GoIRPackageImpl
        var loaderCompleted = false
        pkg = GoIRPackageImpl(
            importPath = "example.com/lazy",
            name = "lazy",
            loader = {
                pkg.addFunction(function("Declared"))
                loaderCompleted = true
            },
        )

        assertThat(pkg.functions).extracting<String> { it.name }.containsExactly("Declared")
        assertThat(loaderCompleted).isTrue()
    }

    @Test
    fun `closed lazy package rejects access locally`() {
        val pkg = GoIRPackageImpl(
            importPath = "example.com/lazy",
            name = "lazy",
            loader = { error("Go IR lazy session is closed") },
        )

        assertThatThrownBy { pkg.functions }
            .isInstanceOf(IllegalStateException::class.java)
            .hasMessageContaining("Go IR lazy session is closed")
    }

    @Test
    fun `function body loads lazily and is cached`() {
        val pkg = GoIRPackageImpl(importPath = "example.com/lazy", name = "lazy")
        lateinit var fn: GoIRFunctionImpl
        var bodyLoadCount = 0
        fn = function("WithBody", pkg) {
            bodyLoadCount++
            fn.setBody(GoIRBodyImpl(fn, emptyList(), null))
        }

        assertThat(fn.hasBody).isTrue()
        assertThat(bodyLoadCount).isZero()
        val firstBody = fn.body
        val secondBody = fn.body
        assertThat(firstBody).isNotNull
        assertThat(secondBody).isSameAs(firstBody)
        assertThat(bodyLoadCount).isEqualTo(1)
    }

    private fun function(
        name: String,
        pkg: GoIRPackageImpl? = null,
        bodyLoader: (() -> Unit)? = null,
    ): GoIRFunctionImpl = GoIRFunctionImpl(
        name = name,
        fullName = "example.com/lazy.$name",
        pkg = pkg,
        signature = GoIRFuncType(
            params = emptyList(),
            results = listOf(GoIRBasicType(GoIRBasicTypeKind.INT)),
            isVariadic = false,
            recv = null,
        ),
        params = emptyList(),
        freeVars = emptyList(),
        position = null,
        isMethod = false,
        isPointerReceiver = false,
        isExported = true,
        isSynthetic = false,
        syntheticKind = null,
        declaredHasBody = bodyLoader != null,
        bodyLoader = bodyLoader,
    )
}
