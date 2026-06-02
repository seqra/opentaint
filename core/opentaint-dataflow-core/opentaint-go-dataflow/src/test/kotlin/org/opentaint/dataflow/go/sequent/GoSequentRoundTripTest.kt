package org.opentaint.dataflow.go.sequent

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.DynamicTest.dynamicTest
import org.junit.jupiter.api.TestFactory
import org.junit.jupiter.api.TestInstance
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import kotlin.io.path.createTempDirectory
import kotlin.io.path.writeText
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GoSequentRoundTripTest {
    private val client = GoIRClient()
    private lateinit var program: GoIRProgram

    @BeforeAll
    fun setup() {
        val dir = createTempDirectory("go-sequent-corpus")
        dir.resolve("go.mod").writeText("module util\ngo 1.18\n")
        dir.resolve("s.go").writeText(CORPUS)
        program = client.buildFromDir(dir, GoIRLoadConfig()).program
    }

    @AfterAll
    fun tearDown() = client.close()

    @TestFactory
    fun roundTrips(): List<DynamicTest> {
        val tests = mutableListOf<DynamicTest>()
        for (fn in program.allFunctions().filter { it.name in CORPUS_FUNCTIONS }) {
            val fixture = SequentFixture(program, fn)
            for (s in fn.scenarios()) {
                tests += dynamicTest("F2F  ${s.label}") { with(fixture) { checkForwardF2F(s) } }
                tests += dynamicTest("Z2F  ${s.label}") { with(fixture) { checkForwardZ2F(s) } }
                if (s.roundTrip) {
                    tests += dynamicTest("pre  ${s.label}") { with(fixture) { checkForwardThenPrecondition(s) } }
                    tests += dynamicTest("back ${s.label}") { with(fixture) { checkBackwardThenForward(s) } }
                }
            }
        }
        return tests
    }

    @TestFactory
    fun corpusCoversAllCategories(): List<DynamicTest> = listOf(
        dynamicTest("at least 200 scenarios generated") {
            val total = program.allFunctions()
                .filter { it.name in CORPUS_FUNCTIONS }
                .sumOf { it.scenarios().size }
            assertTrue(total >= 200, "expected >= 200 scenarios, got $total")
        }
    )

    companion object {
        private val CORPUS_FUNCTIONS = setOf(
            "Deref", "Convert", "SliceOp", "IfaceAssert", "ChangeType", "MakeIface",
            "FieldRead", "FieldReadMethod", "IndexRead", "MapLookup", "ChanRecv", "Extract",
            "Return1", "RetMulti", "Phi", "MapUpdate", "Send", "Concat", "CommaOk",
            "Closure", "RangeMap", "RangeSlice", "GlobalRead", "GlobalStore",
            "FieldStore", "IndexStore", "PtrStore",
        )

        private val CORPUS = """
            package util

            type Box struct{ v interface{}; w interface{} }

            func sink(x interface{}) {}
            func pair() (interface{}, interface{}) { return nil, nil }

            func Deref(p *interface{}) interface{} { return *p }
            func Convert(b []byte) string { return string(b) }
            func SliceOp(s []int) []int { return s[1:2] }
            func IfaceAssert(x interface{}) string { return x.(string) }
            func ChangeType(x MyInt) int { return int(x) }
            func MakeIface(x int) interface{} { return x }
            func FieldRead(b *Box) interface{} { return b.v }
            func (b *Box) FieldReadMethod() interface{} { return b.v }
            func IndexRead(s []interface{}) interface{} { return s[0] }
            func MapLookup(m map[string]interface{}) interface{} { return m["k"] }
            func ChanRecv(c chan interface{}) interface{} { return <-c }
            func Extract() interface{} { a, _ := pair(); return a }
            func Return1(a interface{}) interface{} { return a }
            func RetMulti(a, b interface{}) (interface{}, interface{}) { return a, b }
            func Phi(a, b interface{}, c bool) interface{} { var r interface{}; if c { r = a } else { r = b }; return r }
            func MapUpdate(m map[string]interface{}, k string, v interface{}) { m[k] = v }
            func Send(c chan interface{}, v interface{}) { c <- v }
            func Concat(a, b string) string { return a + b }
            func CommaOk(x interface{}) (string, bool) { s, ok := x.(string); return s, ok }
            func Closure(a interface{}) func() interface{} { return func() interface{} { return a } }
            func RangeMap(m map[string]interface{}) { for k, v := range m { sink(k); sink(v) } }
            func RangeSlice(s []interface{}) { for i, v := range s { sink(i); sink(v) } }

            type MyInt int

            var G interface{}
            func GlobalRead() interface{} { return G }
            func GlobalStore(v interface{}) { G = v }
            func FieldStore(b *Box, v interface{}) { b.v = v }
            func IndexStore(s []interface{}, v interface{}) { s[0] = v }
            func PtrStore(p *interface{}, v interface{}) { *p = v }
        """.trimIndent()
    }
}
