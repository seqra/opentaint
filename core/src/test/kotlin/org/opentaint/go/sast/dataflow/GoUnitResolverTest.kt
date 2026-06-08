package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRPackage
import kotlin.test.assertEquals

class GoUnitResolverTest {
    @Test
    fun `project package resolves to GoPackageUnit`() {
        val resolver = GoUnitResolver()
        val fn = fakeFunction(fakePackage("example.com/main", isStdlib = false, isDependency = false))
        assertEquals(GoUnitResolver.GoPackageUnit("example.com/main"), resolver.resolve(fn))
    }

    @Test
    fun `stdlib package resolves to UnknownUnit`() {
        val resolver = GoUnitResolver()
        val fn = fakeFunction(fakePackage("fmt", isStdlib = true, isDependency = false))
        assertEquals(UnknownUnit, resolver.resolve(fn))
    }

    @Test
    fun `dependency package resolves to UnknownUnit`() {
        val resolver = GoUnitResolver()
        val fn = fakeFunction(fakePackage("github.com/foo/bar", isStdlib = false, isDependency = true))
        assertEquals(UnknownUnit, resolver.resolve(fn))
    }

    @Test
    fun `null package resolves to UnknownUnit`() {
        val resolver = GoUnitResolver()
        val fn = fakeFunction(pkg = null)
        assertEquals(UnknownUnit, resolver.resolve(fn))
    }

    private fun fakePackage(importPath: String, isStdlib: Boolean, isDependency: Boolean): GoIRPackage =
        object : GoIRPackage {
            override val importPath = importPath
            override val name = importPath.substringAfterLast('/')
            override val isStdlib = isStdlib
            override val isDependency = isDependency
            override val functions = emptyList<GoIRFunction>()
            override val namedTypes = emptyList<org.opentaint.ir.go.api.GoIRNamedType>()
            override val globals = emptyList<org.opentaint.ir.go.api.GoIRGlobal>()
            override val constants = emptyList<org.opentaint.ir.go.api.GoIRConst>()
            override val imports = emptyList<GoIRPackage>()
            override val initFunction: GoIRFunction? = null
            override fun findFunction(name: String) = null
            override fun findNamedType(name: String) = null
            override fun findGlobal(name: String) = null
            override fun findConstant(name: String) = null
            override fun allMethods() = emptyList<GoIRFunction>()
        }

    private fun fakeFunction(pkg: GoIRPackage?): GoIRFunction {
        val resolvedPkg = pkg
        return object : GoIRFunction {
            override val name = "fn"
            override val fullName = "${pkg?.importPath ?: "?"}.fn"
            override val pkg = resolvedPkg
            override val signature get() = error("not used")
            override val params = emptyList<org.opentaint.ir.go.api.GoIRParameter>()
            override val freeVars = emptyList<org.opentaint.ir.go.api.GoIRFreeVar>()
            override val position = null
            override val isMethod = false
            override val receiverType = null
            override val isPointerReceiver = false
            override val isExported = true
            override val isSynthetic = false
            override val syntheticKind: String? = null
            override val body = null
            override val parent = null
            override val anonymousFunctions = emptyList<GoIRFunction>()
            override val typeParams = emptyList<org.opentaint.ir.go.api.GoIRTypeParamDecl>()
        }
    }
}
