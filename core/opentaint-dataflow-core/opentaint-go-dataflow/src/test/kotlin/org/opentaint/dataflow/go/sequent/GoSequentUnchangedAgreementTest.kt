package org.opentaint.dataflow.go.sequent

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access
import org.opentaint.dataflow.go.analysis.alias.GoLocalAliasAnalysis
import org.opentaint.dataflow.go.analysis.forEachAliasPathAtStatement
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRFieldStore
import org.opentaint.ir.go.inst.GoIRInst
import kotlin.io.path.createTempDirectory
import kotlin.io.path.writeText
import kotlin.test.assertEquals
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GoSequentUnchangedAgreementTest {
    private val client = GoIRClient()
    private lateinit var program: GoIRProgram

    @BeforeAll
    fun setup() {
        val dir = createTempDirectory("go-sequent-unchanged")
        dir.resolve("go.mod").writeText("module util\ngo 1.18\n")
        dir.resolve("s.go").writeText(
            """
            package util
            type Box struct{ v interface{} }
            type Nested struct{ box *Box }
            func WriteThroughFieldAlias(a *Nested, x interface{}) { y := a.box; y.v = x }
            """.trimIndent()
        )
        program = client.buildFromDir(dir, GoIRLoadConfig()).program
    }

    @AfterAll
    fun tearDown() = client.close()

    private data class Row(val label: String, val forwardUnchanged: Boolean, val backwardUnchanged: Boolean)

    private data class LabeledFact(val label: String, val spec: FactSpec)

    private fun fact(label: String, base: AccessPathBase, vararg path: Accessor) = LabeledFact(label, FactSpec(base, path.toList()))

    private fun SequentFixture.rows(inst: GoIRInst, facts: List<LabeledFact>): List<Row> = facts.map { (label, spec) ->
        val initial = spec.initial()
        val forwardUnchanged = Sequent.Unchanged in ff(inst).propagateFactToFact(initial, spec.final())
        val preconditions = pre(inst).factPrecondition(initial)
        val backwardUnchanged = SequentPrecondition.Unchanged in preconditions

        if (forwardUnchanged) {
            assertTrue(backwardUnchanged, "$label: forward Unchanged requires precondition Unchanged, got $preconditions")
            val selfPreconditions = preconditions.filterIsInstance<PreconditionFactsForInitialFact>()
                .filter { initial in it.preconditionFacts }
            assertEquals(
                emptyList(), selfPreconditions,
                "$label: forward Unchanged fact must not name itself in an explicit precondition",
            )
        }

        Row(label, forwardUnchanged, backwardUnchanged)
    }

    @Test
    fun `sequent flow function and precondition agree on Unchanged at a field read and an aliased field write`() {
        val fn: GoIRFunction = program.allFunctions().first { it.name == "WriteThroughFieldAlias" }
        val instructions = fn.body!!.instructions

        val read = instructions.filterIsInstance<GoIRAssignInst>()
            .single { (GoFlowFunctionUtils.exprToAccess(it.expr, fn) as? Access.RefAccess)?.base is AccessPathBase.Argument }
        val readAccess = GoFlowFunctionUtils.exprToAccess(read.expr, fn) as Access.RefAccess
        val a = readAccess.base
        val box = readAccess.accessor as FieldAccessor
        val readTarget = AccessPathBase.LocalVar(read.register.index)

        val store = instructions.filterIsInstance<GoIRFieldStore>().single()
        val y = GoFlowFunctionUtils.accessPathBase(store.base, fn)
        val x = GoFlowFunctionUtils.accessPathBase(store.value, fn)
        val v = GoFlowFunctionUtils.fieldAccessorFromStore(store)

        assertEquals(AccessPathBase.Argument(0), a)
        assertEquals(AccessPathBase.Argument(1), x)

        val aliases = mutableListOf<Pair<AccessPathBase, List<Accessor>>>()
        GoLocalAliasAnalysis(fn).forEachAliasPathAtStatement(store, y) { base, accessors -> aliases += base to accessors }
        assertTrue(a to listOf<Accessor>(box) in aliases, "the store instance must alias a.box, got $aliases")

        val boxH = GoFlowFunctionUtils.createFieldAccessor(v.className, "h")
        val nestedH = GoFlowFunctionUtils.createFieldAccessor(box.className, "h")
        val unrelated = AccessPathBase.LocalVar(900)

        with(SequentFixture(program, fn)) {
            assertEquals(
                listOf(
                    Row("a.box.h (read field)", forwardUnchanged = false, backwardUnchanged = true),
                    Row("a.h (rest of instance)", forwardUnchanged = false, backwardUnchanged = true),
                    Row("y.h (target)", forwardUnchanged = false, backwardUnchanged = false),
                    Row("u.h (unrelated)", forwardUnchanged = true, backwardUnchanged = true),
                ),
                rows(
                    read,
                    listOf(
                        fact("a.box.h (read field)", a, box, boxH),
                        fact("a.h (rest of instance)", a, nestedH),
                        fact("y.h (target)", readTarget, boxH),
                        fact("u.h (unrelated)", unrelated, boxH),
                    ),
                ),
            )

            assertEquals(
                listOf(
                    Row("y.v.h (written field)", forwardUnchanged = false, backwardUnchanged = false),
                    Row("y.h (rest of instance)", forwardUnchanged = false, backwardUnchanged = true),
                    Row("x.h (value)", forwardUnchanged = false, backwardUnchanged = true),
                    Row("a.box.v.h (aliased written path)", forwardUnchanged = true, backwardUnchanged = true),
                    Row("a.h (rest of alias base)", forwardUnchanged = true, backwardUnchanged = true),
                    Row("u.h (unrelated)", forwardUnchanged = true, backwardUnchanged = true),
                ),
                rows(
                    store,
                    listOf(
                        fact("y.v.h (written field)", y, v, boxH),
                        fact("y.h (rest of instance)", y, boxH),
                        fact("x.h (value)", x, boxH),
                        fact("a.box.v.h (aliased written path)", a, box, v, boxH),
                        fact("a.h (rest of alias base)", a, nestedH),
                        fact("u.h (unrelated)", unrelated, boxH),
                    ),
                ),
            )

            val aliasFact = FactSpec(a, listOf(box, v, boxH)).initial()
            assertEquals(
                setOf(
                    SequentPrecondition.Unchanged,
                    PreconditionFactsForInitialFact(aliasFact, listOf(FactSpec(x, listOf(boxH)).initial())),
                ),
                pre(store).factPrecondition(aliasFact),
                "the aliased written path survives unchanged and may hold the stored value",
            )
        }
    }
}
