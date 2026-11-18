package org.opentaint.ir.go.test.roundtrip

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.TestFactory
import org.junit.jupiter.api.extension.ExtendWith
import org.opentaint.ir.go.test.*

/** Tests that the IR correctly round-trips struct types, field access, and methods. */
@Tag("roundtrip")
@ExtendWith(GoIRTestExtension::class)
class RoundTripStructRealTests {

    @TestFactory
    fun tests(builder: GoIRTestBuilder): List<DynamicTest> {
        val cases = listOf(
            RoundTripTestCase.withInputs("struct-create-field", """
type rtsr_Point struct { X int; Y int }
func rtsr_create(a, b int) int {
    p := rtsr_Point{X: a, Y: b}
    return p.X + p.Y
}""", "rtsr_create(%s, %s)", listOf(listOf("3","4"), listOf("0","0"), listOf("-1","1"), listOf("100","200"))),

            RoundTripTestCase.withInputs("struct-ptr-field-modify", """
type rtsr_Box struct { Val int }
func rtsr_ptr_field(x int) int {
    b := &rtsr_Box{Val: x}
    b.Val *= 3
    return b.Val
}""", "rtsr_ptr_field(%s)", listOf(listOf("5"), listOf("0"), listOf("-2"), listOf("33"))),

            RoundTripTestCase.withInputs("struct-nested", """
type rtsr_Inner struct { V int }
type rtsr_Outer struct { In rtsr_Inner; Extra int }
func rtsr_nested(a, b int) int {
    o := rtsr_Outer{In: rtsr_Inner{V: a}, Extra: b}
    return o.In.V + o.Extra
}""", "rtsr_nested(%s, %s)", listOf(listOf("1","2"), listOf("10","20"), listOf("-5","5"), listOf("0","0"))),

            RoundTripTestCase.withInputs("struct-method-value-recv", """
type rtsr_Counter struct { N int }
func rtsr_inc(c *rtsr_Counter, delta int) { c.N += delta }
func rtsr_method_test(n int) int {
    c := &rtsr_Counter{N: 0}
    for i := 0; i < n; i++ { rtsr_inc(c, i+1) }
    return c.N
}""", "rtsr_method_test(%s)", listOf(listOf("0"), listOf("1"), listOf("5"), listOf("10")), randomRange = 0..50),

            RoundTripTestCase.withInputs("struct-pass-by-value", """
type rtsr_Pair struct { A int; B int }
func rtsr_swap_encode(x, y int) int {
    p := rtsr_Pair{A: x, B: y}
    p.A, p.B = p.B, p.A
    return p.A*100 + p.B
}""", "rtsr_swap_encode(%s, %s)", listOf(listOf("3","7"), listOf("1","1"), listOf("0","99")), randomRange = 0..99),

            RoundTripTestCase.withInputs("struct-slice-field", """
type rtsr_Bag struct { Items []int }
func rtsr_bag_total(n int) int {
    b := rtsr_Bag{Items: make([]int, n)}
    for i := 0; i < n; i++ { b.Items[i] = i * 2 }
    total := 0
    for i := 0; i < n; i++ { total += b.Items[i] }
    return total
}""", "rtsr_bag_total(%s)", listOf(listOf("0"), listOf("1"), listOf("5"), listOf("10")), randomRange = 0..30),

            RoundTripTestCase.withInputs("struct-literal-empty", """
type rtsr_Acc struct { Sum int; Count int }
func rtsr_empty_literal(n int) int {
    a := rtsr_Acc{}
    for i := 0; i < n; i++ { a.Sum += i; a.Count++ }
    return a.Sum*10 + a.Count
}""", "rtsr_empty_literal(%s)", listOf(listOf("0"), listOf("1"), listOf("4")), randomRange = 0..30),

            RoundTripTestCase.withInputs("struct-literal-anonymous-empty", """
func rtsr_anon_literal(n int) int {
    s := struct{ a, b int }{}
    s.a = n
    s.b = n * 2
    return s.a + s.b
}""", "rtsr_anon_literal(%s)", listOf(listOf("0"), listOf("3"), listOf("-4"))),

            RoundTripTestCase.withInputs("struct-literal-reassign", """
type rtsr_Span struct { From int; To int }
func rtsr_reassign(a, b int) int {
    s := rtsr_Span{From: a, To: b}
    if a > b { s = rtsr_Span{From: b} }
    p := &s
    return p.From*100 + s.To
}""", "rtsr_reassign(%s, %s)", listOf(listOf("1","2"), listOf("5","3"), listOf("0","0")), randomRange = 0..99),

            RoundTripTestCase.withInputs("struct-literal-copy", """
type rtsr_Vec struct { X int; Y int }
func rtsr_copy(a, b int) int {
    p := rtsr_Vec{X: a, Y: b}
    q := p
    q.X = b
    return p.X*10000 + q.X*100 + q.Y
}""", "rtsr_copy(%s, %s)", listOf(listOf("1","2"), listOf("7","7"), listOf("0","9")), randomRange = 0..99),

            RoundTripTestCase.withInputs("struct-literal-in-array", """
type rtsr_Cell struct { V int }
func rtsr_cells(a, b int) int {
    cells := [2]rtsr_Cell{{V: a}, {V: b}}
    cells[0] = rtsr_Cell{}
    return cells[0].V*100 + cells[1].V
}""", "rtsr_cells(%s, %s)", listOf(listOf("1","2"), listOf("9","0"), listOf("5","5")), randomRange = 0..99),

            RoundTripTestCase.withInputs("array-literal-empty", """
func rtsr_empty_array(n int) int {
    d := [4]int{}
    for i := 0; i < 4; i++ { d[i] = n + i }
    total := 0
    for i := 0; i < 4; i++ { total += d[i] }
    return total
}""", "rtsr_empty_array(%s)", listOf(listOf("0"), listOf("1"), listOf("10")), randomRange = 0..99),
        )
        return BatchRoundTripRunner.runBatchAndCreateTests(cases, builder)
    }
}
