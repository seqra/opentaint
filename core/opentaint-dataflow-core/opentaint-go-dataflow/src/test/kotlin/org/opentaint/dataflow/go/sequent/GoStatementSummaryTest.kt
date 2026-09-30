package org.opentaint.dataflow.go.sequent

import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary.Edge
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.analysis.GoStatementSummary
import org.opentaint.dataflow.go.analysis.alias.GoLocalAliasAnalysis
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.ir.go.expr.GoIRLookupExpr
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRFieldStore
import org.opentaint.ir.go.inst.GoIRInst
import kotlin.io.path.createTempDirectory
import kotlin.io.path.writeText
import kotlin.test.assertEquals
import kotlin.test.assertNull

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GoStatementSummaryTest {
    private val client = GoIRClient()
    private lateinit var program: GoIRProgram

    @BeforeAll
    fun setup() {
        val dir = createTempDirectory("go-statement-summary")
        dir.resolve("go.mod").writeText("module util\ngo 1.18\n")
        dir.resolve("s.go").writeText(
            """
            package util
            type Box struct{ v interface{}; w interface{} }
            func FieldStore(b *Box, v interface{}) { b.v = v }
            func Lookup(m map[string]interface{}) interface{} { x, ok := m["k"]; if ok { return x }; return nil }
            """.trimIndent()
        )
        program = client.buildFromDir(dir, GoIRLoadConfig()).program
    }

    @AfterAll
    fun tearDown() = client.close()

    private fun func(name: String): GoIRFunction = program.allFunctions().first { it.name == name }

    private fun SequentFixture.build(inst: GoIRInst): StatementSummary =
        GoStatementSummary.build(apManager, inst, fn, GoLocalAliasAnalysis(fn))

    private fun SequentFixture.buildReversed(inst: GoIRInst): StatementSummary =
        GoStatementSummary.buildReversed(apManager, inst, fn, GoLocalAliasAnalysis(fn))

    private fun StatementSummary.edgesOf(base: AccessPathBase): List<Edge>? = find(base)?.edges?.toList()

    private fun StatementSummary.forward(fact: FinalFactAp): Set<FinalFactAp> {
        val produced = hashSetOf<FinalFactAp>()
        SummaryApplication.transfer(this, fact, FactTypeChecker.Dummy, { produced += it }, { })
        return produced
    }

    @Test
    fun `field store writes the field strongly`() {
        val fn = func("FieldStore")
        val store = fn.body!!.instructions.filterIsInstance<GoIRFieldStore>().single()
        val instance = GoFlowFunctionUtils.accessPathBase(store.base, fn)
        val value = GoFlowFunctionUtils.accessPathBase(store.value, fn)
        val field = GoFlowFunctionUtils.fieldAccessorFromStore(store)
        val other = GoFlowFunctionUtils.createFieldAccessor(field.className, "w")

        with(SequentFixture(program, fn)) {
            val onInstance = FactSpec(instance, emptyList())
            val onField = FactSpec(instance, listOf(field))
            val onOther = FactSpec(instance, listOf(other))
            val onValue = FactSpec(value, emptyList())

            val summary = build(store)
            assertEquals(listOf(Edge(onInstance.initial().exclude(field), onInstance.initial())), summary.edgesOf(instance))
            assertEquals(
                listOf(Edge(onValue.initial(), onValue.initial()), Edge(onValue.initial(), onField.initial())),
                summary.edgesOf(value),
            )

            assertEquals(setOf(onValue.final(), onField.final()), summary.forward(onValue.final()))
            assertEquals(emptySet(), summary.forward(onField.final()))
            assertEquals(setOf(onOther.final()), summary.forward(onOther.final()))

            val reversed = buildReversed(store)
            assertEquals(listOf(onValue.initial()), SummaryApplication.preconditionFacts(reversed, onField.initial()))
            assertEquals(listOf(onOther.initial()), SummaryApplication.preconditionFacts(reversed, onOther.initial()))
            assertEquals(listOf(onValue.initial()), SummaryApplication.preconditionFacts(reversed, onValue.initial()))
        }
    }

    @Test
    fun `comma-ok lookup reads the element into the value slot`() {
        val fn = func("Lookup")
        val lookup = fn.body!!.instructions.filterIsInstance<GoIRAssignInst>()
            .single { (it.expr as? GoIRLookupExpr)?.commaOk == true }
        val map = GoFlowFunctionUtils.accessPathBase((lookup.expr as GoIRLookupExpr).x, fn)
        val result = AccessPathBase.LocalVar(lookup.register.index)
        val valueSlot = GoFlowFunctionUtils.tupleFieldAccessor(0)
        val okSlot = GoFlowFunctionUtils.tupleFieldAccessor(1)

        with(SequentFixture(program, fn)) {
            val onMap = FactSpec(map, emptyList())
            val onElement = FactSpec(map, listOf(ElementAccessor))
            val onValue = FactSpec(result, listOf(valueSlot))
            val onOk = FactSpec(result, listOf(okSlot))

            val summary = build(lookup)
            assertEquals(emptyList(), summary.edgesOf(result))
            assertEquals(
                listOf(
                    Edge(onMap.initial().exclude(ElementAccessor), onMap.initial()),
                    Edge(onElement.initial(), onElement.initial()),
                    Edge(onElement.initial(), onValue.initial()),
                ),
                summary.edgesOf(map),
            )

            assertEquals(setOf(onElement.final(), onValue.final()), summary.forward(onElement.final()))
            assertEquals(emptySet(), summary.forward(onValue.final()))

            val reversed = buildReversed(lookup)
            assertEquals(listOf(onElement.initial()), SummaryApplication.preconditionFacts(reversed, onValue.initial()))
            assertEquals(emptyList(), SummaryApplication.preconditionFacts(reversed, onOk.initial()))
            assertNull(SummaryApplication.preconditionFacts(reversed, FactSpec(AccessPathBase.LocalVar(900), emptyList()).initial()))
        }
    }

    private object SummaryApplication : MethodSequentFlowFunction, MethodSequentPrecondition {
        override fun propagateZeroToZero(): Set<Sequent> = error("unused")
        override fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<Sequent> = error("unused")
        override fun propagateFactToFact(initialFactAp: InitialFactAp, currentFactAp: FinalFactAp): Set<Sequent> = error("unused")
        override fun propagateNDFactToFact(initialFacts: Set<InitialFactAp>, currentFactAp: FinalFactAp): Set<Sequent> = error("unused")
        override fun factPrecondition(fact: InitialFactAp): Set<SequentPrecondition> = error("unused")
    }
}
