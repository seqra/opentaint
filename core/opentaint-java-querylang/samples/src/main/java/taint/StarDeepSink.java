package taint;

import base.RuleSample;
import base.RuleSet;

/**
 * Starred SINK, taint hidden at graduated field depths. A plain source taints a field N levels
 * down; the starred whole-object sink `sink($*Y)` must observe the any-field taint.
 *
 * CHARACTERIZED GAP (2026-07-20): the starred sink's any-field check matches a CONCRETE field
 * mark only at depth 1; a concrete mark buried 2+ levels deep is NOT observed, regardless of
 * the any-accessor unroll strategy. (Contrast StarSourceAndSink, where the whole-object SOURCE
 * star produces an abstract any-field taint that a deep extraction does observe.) The depth-2+
 * cases are therefore parked as `KnownFn*` classes — not matched by the Positive/Negative
 * filter, so they neither run nor assert — until the any-field condition is made depth-recursive.
 */
@RuleSet("taint/StarDeepSink.yaml")
public abstract class StarDeepSink implements RuleSample {
    String src() { return "tainted"; }
    void sink(L0 b) {}

    static final class L0 { public String v0; public L1 f; }
    static final class L1 { public String v1; public L2 f; }
    static final class L2 { public String v2; public L3 f; }
    static final class L3 { public String v3; public L4 f; }
    static final class L4 { public String v; }

    private static L0 build() {
        L0 o = new L0();
        o.f = new L1();
        o.f.f = new L2();
        o.f.f.f = new L3();
        o.f.f.f.f = new L4();
        return o;
    }

    // Positive (WORKS): taint at field depth 1 — the starred sink observes it.
    final static class PositiveDepth1 extends StarDeepSink {
        @Override public void entrypoint() {
            L0 o = build();
            o.v0 = src();   // depth-1 field
            sink(o);
        }
    }

    // KNOWN GAP: depth-2 concrete field mark is not observed by the starred sink.
    final static class KnownFnDepth2 extends StarDeepSink {
        @Override public void entrypoint() {
            L0 o = build();
            o.f.v1 = src();
            sink(o);
        }
    }

    // KNOWN GAP: depth-5 concrete field mark is not observed by the starred sink.
    final static class KnownFnDepth5 extends StarDeepSink {
        @Override public void entrypoint() {
            L0 o = build();
            o.f.f.f.f.v = src();
            sink(o);
        }
    }

    // Negative: no field ever tainted.
    final static class NegativeCleanObject extends StarDeepSink {
        @Override public void entrypoint() {
            L0 o = build();
            o.f.f.f.f.v = "safe";
            sink(o);
        }
    }
}
