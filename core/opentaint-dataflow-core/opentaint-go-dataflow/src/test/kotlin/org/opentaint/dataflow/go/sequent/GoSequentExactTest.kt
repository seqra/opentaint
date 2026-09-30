package org.opentaint.dataflow.go.sequent

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo.Flow
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.dataflow.go.analysis.forEachAliasPathAtStatement
import org.opentaint.dataflow.go.analysis.alias.GoLocalAliasAnalysis
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRFieldStore
import org.opentaint.ir.go.inst.GoIRPhi
import org.opentaint.ir.go.value.GoIRConstValue
import kotlin.io.path.createTempDirectory
import kotlin.io.path.writeText
import kotlin.test.assertEquals
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GoSequentExactTest {
    private val client = GoIRClient()
    private lateinit var program: GoIRProgram

    @BeforeAll
    fun setup() {
        val dir = createTempDirectory("go-sequent-exact")
        dir.resolve("go.mod").writeText("module util\ngo 1.18\n")
        dir.resolve("s.go").writeText(
            """
            package util
            type Box struct{ v interface{} }
            func Deref(p *interface{}) interface{} { return *p }
            func FieldRead(b *Box) interface{} { return b.v }
            func Phi(a, b interface{}, c bool) interface{} { var r interface{}; if c { r = a } else { r = b }; return r }
            type Pair struct{ value string; extra string }
            func CopyThenOverwrite(s string) string { o := Pair{value: s, extra: "x"}; c := o; o.value = "safe"; return c.value }
            """.trimIndent()
        )
        program = client.buildFromDir(dir, GoIRLoadConfig()).program
    }

    @AfterAll
    fun tearDown() = client.close()

    private fun func(name: String): GoIRFunction = program.allFunctions().first { it.name == name }

    private val unrelated = AccessPathBase.LocalVar(900)

    @Test
    fun `simple copy gen kill passthrough`() {
        val fn = func("Deref")
        val fixture = SequentFixture(program, fn)
        val assign = fn.body!!.instructions.filterIsInstance<GoIRAssignInst>()
            .first { GoFlowFunctionUtils.exprToAccess(it.expr, fn) is Access.Simple }
        val src = (GoFlowFunctionUtils.exprToAccess(assign.expr, fn) as Access.Simple).base
        val dst = AccessPathBase.LocalVar(assign.register.index)

        with(fixture) {
            val ff = ff(assign)
            val onSrc = FactSpec(src, emptyList())
            val onDst = FactSpec(dst, emptyList())
            val onOther = FactSpec(unrelated, emptyList())

            assertEquals(
                setOf(
                    Sequent.FactToFact(onSrc.initial(), onSrc.final(), Flow),
                    Sequent.FactToFact(onSrc.initial(), onDst.final(), Flow),
                ),
                ff.propagateFactToFact(onSrc.initial(), onSrc.final()),
                "fact on source survives and propagates to destination",
            )
            assertEquals(
                emptySet(),
                ff.propagateFactToFact(onDst.initial(), onDst.final()),
                "fact on destination is killed by the overwrite",
            )
            assertEquals(
                setOf<Sequent>(Sequent.Unchanged),
                ff.propagateFactToFact(onOther.initial(), onOther.final()),
                "unrelated fact passes through unchanged",
            )

            assertEquals(
                setOf(
                    Sequent.ZeroToFact(onSrc.final(ExclusionSet.Universe), Flow),
                    Sequent.ZeroToFact(onDst.final(ExclusionSet.Universe), Flow),
                ),
                ff.propagateZeroToFact(onSrc.final(ExclusionSet.Universe)),
            )

            assertTrue(Sequent.ZeroToZero in ff.propagateZeroToZero())

            val pre = pre(assign).factPrecondition(onDst.initial())
            assertEquals(
                setOf<SequentPrecondition>(PreconditionFactsForInitialFact(onDst.initial(), listOf(onSrc.initial()))),
                pre,
            )
            assertEquals(
                setOf<SequentPrecondition>(SequentPrecondition.Unchanged),
                pre(assign).factPrecondition(onOther.initial()),
            )
        }
    }

    @Test
    fun `field read strips accessor`() {
        val fn = func("FieldRead")
        val fixture = SequentFixture(program, fn)
        val assign = fn.body!!.instructions.filterIsInstance<GoIRAssignInst>()
            .first { GoFlowFunctionUtils.exprToAccess(it.expr, fn) is Access.RefAccess }
        val ref = GoFlowFunctionUtils.exprToAccess(assign.expr, fn) as Access.RefAccess
        val dst = AccessPathBase.LocalVar(assign.register.index)

        with(fixture) {
            val ff = ff(assign)
            val onField = FactSpec(ref.base, listOf(ref.accessor))
            val onDst = FactSpec(dst, emptyList())

            assertEquals(
                setOf(
                    Sequent.FactToFact(onField.initial(), onField.final(), Flow),
                    Sequent.FactToFact(onField.initial(), onDst.final(), Flow),
                ),
                ff.propagateFactToFact(onField.initial(), onField.final()),
                "reading base.field into the register strips the field accessor",
            )

            val pre = pre(assign).factPrecondition(onDst.initial())
            assertEquals(
                setOf<SequentPrecondition>(PreconditionFactsForInitialFact(onDst.initial(), listOf(onField.initial()))),
                pre,
            )
        }
    }

    @Test
    fun `phi merges all edges in precondition`() {
        val fn = func("Phi")
        val fixture = SequentFixture(program, fn)
        val phi = fn.body!!.instructions.filterIsInstance<GoIRPhi>().first()
        val dst = AccessPathBase.LocalVar(phi.register.index)
        val edgeBases = phi.edges.values.map { GoFlowFunctionUtils.accessPathBase(it, fn) }

        with(fixture) {
            val onDst = FactSpec(dst, emptyList())
            val pre = pre(phi).factPrecondition(onDst.initial())
            val expectedPres = edgeBases.map { FactSpec(it, emptyList()).initial() }
            assertEquals(
                setOf<SequentPrecondition>(PreconditionFactsForInitialFact(onDst.initial(), expectedPres)),
                pre,
                "phi precondition lists every incoming edge value",
            )

            assertEquals(emptySet(), ff(phi).propagateFactToFact(onDst.initial(), onDst.final()))
        }
    }

    @Test
    fun `alias of an overwritten field is unchanged with the stored value as precondition`() {
        val fn = func("CopyThenOverwrite")
        val fixture = SequentFixture(program, fn)
        val store = fn.body!!.instructions.filterIsInstance<GoIRFieldStore>()
            .single { (it.value as? GoIRConstValue)?.value?.toString()?.contains("safe") == true }
        val instance = GoFlowFunctionUtils.accessPathBase(store.base, fn)
        val stored = GoFlowFunctionUtils.accessPathBase(store.value, fn)
        val field = GoFlowFunctionUtils.fieldAccessorFromStore(store)
        val aliases = mutableListOf<AccessPathBase>()
        GoLocalAliasAnalysis(fn).forEachAliasPathAtStatement(store, instance) { base, accessors ->
            if (base != instance && accessors.isEmpty()) aliases += base
        }
        assertTrue(aliases.isNotEmpty(), "the copy must alias the overwritten instance")

        with(fixture) {
            for (alias in aliases) {
                val onAliasField = FactSpec(alias, listOf(field))
                assertEquals(
                    setOf<Sequent>(Sequent.Unchanged),
                    ff(store).propagateFactToFact(onAliasField.initial(), onAliasField.final()),
                    "the forward flow does not touch the alias",
                )
                assertEquals(
                    setOf(
                        SequentPrecondition.Unchanged,
                        PreconditionFactsForInitialFact(onAliasField.initial(), listOf(FactSpec(stored, emptyList()).initial())),
                    ),
                    pre(store).factPrecondition(onAliasField.initial()),
                    "the alias survives unchanged and may hold the stored value",
                )
            }
        }
    }
}
