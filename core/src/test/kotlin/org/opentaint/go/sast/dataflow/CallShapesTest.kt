package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.PassThrough
import org.opentaint.go.config.GoConfigLoader
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class CallShapesTest : AnalysisTest() {

    override val commonPassRules: List<PassThrough> =
        GoConfigLoader.getConfig()?.passThrough ?: emptyList()

    // 1. DIRECT non-method
    @Test fun directNonMethod001T() = assertReachable("test.directNonMethod001T")
    @Test fun directNonMethod002F() = assertNotReachable("test.directNonMethod002F")

    // 2. DIRECT value-method
    @Test fun directValueMethod001T() = assertReachable("test.directValueMethod001T")
    @Test fun directValueMethod002F() = assertNotReachable("test.directValueMethod002F")

    // 3. DIRECT pointer-method
    @Test fun directPointerMethod001T() = assertReachable("test.directPointerMethod001T")
    @Test fun directPointerMethod002F() = assertNotReachable("test.directPointerMethod002F")

    // 4. INVOKE (interface dispatch)
    @Test fun invoke001T() = assertReachable("test.invoke001T")
    @Test fun invoke002F() = assertNotReachable("test.invoke002F")

    // 5. DYNAMIC plain (function-valued variable)
    @Test fun dynamicPlain001T() = assertReachable("test.dynamicPlain001T")
    @Test fun dynamicPlain002F() = assertNotReachable("test.dynamicPlain002F")

    // 6. DYNAMIC bound-method
    @Test fun dynamicBoundMethod001T() = assertReachable("test.dynamicBoundMethod001T")
    @Test fun dynamicBoundMethod002F() = assertNotReachable("test.dynamicBoundMethod002F")

    // 7. Method expression (T.M)
    @Test fun methodExpression001T() = assertReachable("test.methodExpression001T")
    @Test fun methodExpression002F() = assertNotReachable("test.methodExpression002F")

    // 8. Embedded promoted method
    @Test fun embeddedPromoted001T() = assertReachable("test.embeddedPromoted001T")
    @Test fun embeddedPromoted002F() = assertNotReachable("test.embeddedPromoted002F")

    // 9. Builtin (append)
    @Test fun builtin001T() = assertReachable("test.builtin001T")
    @Test fun builtin002F() = assertNotReachable("test.builtin002F")

    // 10. Unresolved DYNAMIC (function from map lookup)
    @Test fun unresolvedDynamic001T() = assertReachable("test.unresolvedDynamic001T")
    @Test fun unresolvedDynamic002F() = assertNotReachable("test.unresolvedDynamic002F")

    // 11. Generic monomorphised
    @Test fun genericMonomorphised001T() = assertReachable("test.genericMonomorphised001T")
    @Test fun genericMonomorphised002F() = assertNotReachable("test.genericMonomorphised002F")
}
