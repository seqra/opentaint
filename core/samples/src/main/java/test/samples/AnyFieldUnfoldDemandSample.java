package test.samples;

/**
 * A unit-scale reproduction of the mark-unfold demand iterating on its own output.
 *
 * `Cell` is SELF-SIMILAR in six ways: every one of a..f is a `Cell` again. `cyclic` closes all six
 * back onto the same object inside a loop, so after the loop EVERY word over {a..f} is a live
 * access path off the returned object and the taint sits at the end of all of them. The chain of
 * forwarding frames then carries the container down to the sink as a formal parameter, which is
 * what makes the sink's any-field condition raise its request on fact-to-fact edges.
 *
 * The sink condition asks for a mark under an arbitrary field of argument 0. Entering the frame
 * with the container abstracted, the mark is not in view, so a TaintMarkFieldUnfoldRequest is
 * raised; the answer splits out the accessors that lead to the mark, which produces
 * `arg0.<accessor>.[any]` -- an abstraction ending in `[any]` again, one accessor deeper, asking
 * the same question. On this shape the accessors handed back are the same six every time, so the
 * iteration has no fixed point.
 *
 * The flow is a genuine true positive: `cyclic` really does store the source into a field of the
 * object the sink receives.
 */
public class AnyFieldUnfoldDemandSample {

    public static class Cell {
        public Cell a, b, c, d, e, f;
        public String value;
    }

    public String source() {
        return "tainted";
    }

    public void sink(Cell c) { }

    private void touch(Cell c) { }

    /** Closes the cycle on every field, on a back edge, so the access paths have no bottom. */
    private Cell cyclic(String v, int n) {
        Cell c = new Cell();
        c.value = v;
        for (int i = 0; i < n; i++) {
            c.a = c;
            c.b = c;
            c.c = c;
            c.d = c;
            c.e = c;
            c.f = c;
        }
        return c;
    }


    // ---- a chain of 20 frames, each entered with the container as a formal parameter ----
    private void f20_00(Cell c) { sink(c.a); }
    private void f20_01(Cell c) { f20_00(c); }
    private void f20_02(Cell c) { touch(c.c); f20_01(c); }
    private void f20_03(Cell c) { f20_02(c); }
    private void f20_04(Cell c) { touch(c.e); f20_03(c); }
    private void f20_05(Cell c) { f20_04(c); }
    private void f20_06(Cell c) { touch(c.a); f20_05(c); }
    private void f20_07(Cell c) { f20_06(c); }
    private void f20_08(Cell c) { touch(c.c); f20_07(c); }
    private void f20_09(Cell c) { f20_08(c); }
    private void f20_10(Cell c) { touch(c.e); f20_09(c); }
    private void f20_11(Cell c) { f20_10(c); }
    private void f20_12(Cell c) { touch(c.a); f20_11(c); }
    private void f20_13(Cell c) { f20_12(c); }
    private void f20_14(Cell c) { touch(c.c); f20_13(c); }
    private void f20_15(Cell c) { f20_14(c); }
    private void f20_16(Cell c) { touch(c.e); f20_15(c); }
    private void f20_17(Cell c) { f20_16(c); }
    private void f20_18(Cell c) { touch(c.a); f20_17(c); }
    private void f20_19(Cell c) { f20_18(c); }

    public void chain20() { f20_19(cyclic(source(), 2)); }

    // ---- a chain of 40 frames, each entered with the container as a formal parameter ----
    private void f40_00(Cell c) { sink(c.a); }
    private void f40_01(Cell c) { f40_00(c); }
    private void f40_02(Cell c) { touch(c.c); f40_01(c); }
    private void f40_03(Cell c) { f40_02(c); }
    private void f40_04(Cell c) { touch(c.e); f40_03(c); }
    private void f40_05(Cell c) { f40_04(c); }
    private void f40_06(Cell c) { touch(c.a); f40_05(c); }
    private void f40_07(Cell c) { f40_06(c); }
    private void f40_08(Cell c) { touch(c.c); f40_07(c); }
    private void f40_09(Cell c) { f40_08(c); }
    private void f40_10(Cell c) { touch(c.e); f40_09(c); }
    private void f40_11(Cell c) { f40_10(c); }
    private void f40_12(Cell c) { touch(c.a); f40_11(c); }
    private void f40_13(Cell c) { f40_12(c); }
    private void f40_14(Cell c) { touch(c.c); f40_13(c); }
    private void f40_15(Cell c) { f40_14(c); }
    private void f40_16(Cell c) { touch(c.e); f40_15(c); }
    private void f40_17(Cell c) { f40_16(c); }
    private void f40_18(Cell c) { touch(c.a); f40_17(c); }
    private void f40_19(Cell c) { f40_18(c); }
    private void f40_20(Cell c) { touch(c.c); f40_19(c); }
    private void f40_21(Cell c) { f40_20(c); }
    private void f40_22(Cell c) { touch(c.e); f40_21(c); }
    private void f40_23(Cell c) { f40_22(c); }
    private void f40_24(Cell c) { touch(c.a); f40_23(c); }
    private void f40_25(Cell c) { f40_24(c); }
    private void f40_26(Cell c) { touch(c.c); f40_25(c); }
    private void f40_27(Cell c) { f40_26(c); }
    private void f40_28(Cell c) { touch(c.e); f40_27(c); }
    private void f40_29(Cell c) { f40_28(c); }
    private void f40_30(Cell c) { touch(c.a); f40_29(c); }
    private void f40_31(Cell c) { f40_30(c); }
    private void f40_32(Cell c) { touch(c.c); f40_31(c); }
    private void f40_33(Cell c) { f40_32(c); }
    private void f40_34(Cell c) { touch(c.e); f40_33(c); }
    private void f40_35(Cell c) { f40_34(c); }
    private void f40_36(Cell c) { touch(c.a); f40_35(c); }
    private void f40_37(Cell c) { f40_36(c); }
    private void f40_38(Cell c) { touch(c.c); f40_37(c); }
    private void f40_39(Cell c) { f40_38(c); }

    public void chain40() { f40_39(cyclic(source(), 2)); }
}
