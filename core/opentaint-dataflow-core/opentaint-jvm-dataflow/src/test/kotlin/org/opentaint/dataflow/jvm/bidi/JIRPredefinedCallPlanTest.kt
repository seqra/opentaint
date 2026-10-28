package org.opentaint.dataflow.jvm.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.jvm.BasicTestUtils
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver.MethodResolutionResult
import org.opentaint.dataflow.jvm.bidi.fixtures.CallRules
import org.opentaint.dataflow.jvm.bidi.fixtures.JIRCallTestFixtures
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRInstList
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRStaticCallExpr
import org.opentaint.ir.api.jvm.cfg.TypedMethodRef
import kotlin.test.*

class JIRPredefinedCallPlanTest : BasicTestUtils() {
    private val v by lazy { JIRCallTestFixtures(cp) }
    private fun model(zero: Boolean = true) = CompleteMethodSummary(
        normal = (if (zero) listOf(SummarySchema.ZeroIdentity) else emptyList()) +
            SummarySchema.PrefixFlowIdentity(STATIC, listOf(ClassStaticAccessor("Registry"))),
        touched = setOf(STATIC),
    )
    private fun target(model: CompleteMethodSummary): JIRMethod =
        object : JIRMethod by v.method("target"), PredefinedSummaryMethod {
            override val predefinedSummary = model
            override val instList: JIRInstList<JIRInst> get() = error("A predefined body must not be read")
        }
    private fun resolution(method: JIRMethod) = MethodResolutionResult.ConcreteMethod(MethodWithContext(method, EmptyMethodContext))

    @Test fun `complete target is selected before body or entrypoint loading and has no fallback`() {
        val model = model()
        val target = target(model)
        val rules = CallRules()
        val plan = v.builder(rules = rules, resolutions = listOf(resolution(target))).build()
        assertTrue(plan.stages.none { it is CallStage.Callees })
        assertTrue(plan.stages.filterIsInstance<CallStage.Edges>().none {
            it.kind == StageKind.UNRESOLVED || it.kind == StageKind.CONSTRUCTOR
        })
        val stage = plan.stages.filterIsInstance<CallStage.Predefined>().single()
        assertSame(target, stage.target)
        assertSame(model, stage.model)
        assertEquals(CallPoint.ADDED, stage.from)
        assertEquals(CallPoint.RETURNED, stage.to)
        assertTrue(STATIC in plan.touched)
        assertTrue(STATIC in plan.reversed().touched)
        assertTrue(plan.zeroCanReturn)
        assertTrue(plan.reversed().zeroCanReturn)
        assertTrue(rules.queries.any { it.kind == "source" && !it.allRelevant })
        assertTrue(rules.queries.any { it.kind == "sink" })
        assertTrue(rules.queries.any { it.kind == "cleaner" && !it.allRelevant })
    }

    @Test fun `complete model without ZERO row has neither implicit control lane`() {
        val plan = v.builder(resolutions = listOf(resolution(target(model(false))))).build()
        assertFalse(plan.zeroCanReturn)
        assertFalse(plan.reversed().zeroCanReturn)
        assertTrue(plan.stages.filterIsInstance<CallStage.Edges>().single { it.kind == StageKind.SOURCES }
            .summary.edges.none { it.edge == ZERO_KEEP })
        assertTrue(plan.stages.filterIsInstance<CallStage.Predefined>().single().summary.edges.none {
            it.edge.from.base == AccessPathBase.Zero
        })
    }

    @Test fun `mixed dispatch preserves analyzed target union without duplicate modeled analyzer`() {
        val target = target(model(false))
        val plan = v.builder(resolutions = listOf(resolution(target), v.resolved())).build()
        assertEquals(listOf(v.key("target")), plan.stages.filterIsInstance<CallStage.Callees>().single().callees)
        assertEquals(listOf(target), plan.stages.filterIsInstance<CallStage.Predefined>().map { it.target })
        assertTrue(plan.zeroCanReturn)
        assertTrue(plan.stages.filterIsInstance<CallStage.Edges>().none { it.kind == StageKind.UNRESOLVED })
    }

    @Test fun `registered direct static target wins over ordinary unresolved resolution`() {
        val original = v.call("staticCall") as JIRAssignInst
        val call = v.expr(original) as JIRStaticCallExpr
        val target = target(model())
        val typed = object : org.opentaint.ir.api.jvm.JIRTypedMethod by call.method { override val method = target }
        val ref = object : TypedMethodRef { override val name = typed.name; override val method = typed }
        val statement = JIRAssignInst(original.location, original.lhv, JIRStaticCallExpr(ref, call.args))
        val plan = v.builder(statement, resolutions = listOf(MethodResolutionResult.MethodResolutionFailed)).build()
        assertSame(target, plan.stages.filterIsInstance<CallStage.Predefined>().single().target)
        assertTrue(plan.stages.filterIsInstance<CallStage.Edges>().none { it.kind == StageKind.UNRESOLVED })
    }

    @Test fun `unregistered same-name target remains an ordinary analyzed target`() {
        val plan = v.builder(resolutions = listOf(v.resolved())).build()
        assertTrue(plan.stages.none { it is CallStage.Predefined })
        assertEquals(listOf(v.key("target")), plan.stages.filterIsInstance<CallStage.Callees>().single().callees)
    }
}
