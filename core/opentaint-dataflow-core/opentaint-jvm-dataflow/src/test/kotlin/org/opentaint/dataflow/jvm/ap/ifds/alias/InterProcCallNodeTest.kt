package org.opentaint.dataflow.jvm.ap.ifds.alias

import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.jvm.ap.ifds.alias.DSUAliasAnalysis.ResolvedCallMethod
import org.opentaint.dataflow.jvm.ap.ifds.alias.JIRIntraProcAliasAnalysis.JIRInstGraph
import org.opentaint.dataflow.jvm.ap.ifds.alias.RefValue.Local
import org.opentaint.ir.api.jvm.JIRMethod
import java.lang.reflect.Proxy
import kotlin.test.Test
import kotlin.test.assertNull

class InterProcCallNodeTest {
    @Test
    fun `call resolution rejects a target with incompatible arity`() {
        val callMethod = method(parameterCount = 0)
        val incompatibleTarget = method(parameterCount = 1)
        val call = Stmt.Call(
            method = callMethod,
            lValue = null,
            instance = null,
            args = emptyList(),
            originalIdx = 0,
        )
        val resolver = object : CallResolver {
            override fun resolveMethodCall(
                callStmt: Stmt.Call,
                level: Int,
            ): List<JIRMethod> = listOf(incompatibleTarget)

            override fun buildMethodGraph(method: JIRMethod): JIRInstGraph =
                error("An incompatible target must be rejected before its graph is built")

            override fun externalCallModel(
                method: JIRMethod,
            ): List<ExternalCallModelProvider.ExternalAssign> = emptyList()
        }
        val node = CallTreeNode(ContextInfo.rootContext, unusedInstEvalContext)

        val resolved: Map<JIRMethod, ResolvedCallMethod>? = node.resolveCall(call, resolver)

        assertNull(resolved)
    }

    private val unusedInstEvalContext = object : InstEvalContext {
        override fun createThis(isOuter: Boolean): Value = error("unused")
        override fun createArg(idx: Int): Value = error("unused")
        override fun createLocal(idx: Int): Local = error("unused")
    }

    private fun method(parameterCount: Int): JIRMethod {
        val type = JIRMethod::class.java
        return Proxy.newProxyInstance(type.classLoader, arrayOf(type)) { proxy, invoked, args ->
            when (invoked.name) {
                "getParameters" -> List(parameterCount) { null }
                "equals" -> proxy === args?.singleOrNull()
                "hashCode" -> System.identityHashCode(proxy)
                "toString" -> "method(arity=$parameterCount)"
                else -> error("Unexpected JIRMethod member: ${invoked.name}")
            }
        } as JIRMethod
    }
}
