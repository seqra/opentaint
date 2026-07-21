package taint;

import base.RuleSample;
import base.RuleSet;

/**
 * Reproduces, WITHOUT the star operator, a taint false negative for a field-of-a-field store.
 *
 * `o.f.v = src()` (depth 2) is lowered by the IR to `%0 = o.f; %0.v = src()`, so the taint fact is
 * rooted at the temp `%0`, not at `o.f.v`. The taint is therefore not carried on the base object
 * `o`, and is lost when `o` is passed interprocedurally (the argument must carry `o.f.v`) or read
 * back precisely. A depth-1 store (`x.v = src()`) works because `x` is the base directly, no temp.
 */
@RuleSet("taint/DeepFieldStoreFn.yaml")
public abstract class DeepFieldStoreFn implements RuleSample {
    String src() { return "tainted"; }
    void sink(String s) {}

    static final class L0 { public L1 f; }
    static final class L1 { public String v; }

    // Baseline (expected WORKS): depth-1 field store, observed interprocedurally.
    final static class PositiveDepth1Interproc extends DeepFieldStoreFn {
        @Override public void entrypoint() {
            L1 x = new L1();
            x.v = src();          // depth-1 store on the local x
            leak(x);
        }
        void leak(L1 p) { sink(p.v); }
    }

    // Depth-2 field store, observed interprocedurally via the base object.
    final static class PositiveDepth2Interproc extends DeepFieldStoreFn {
        @Override public void entrypoint() {
            L0 o = new L0();
            o.f = new L1();
            o.f.v = src();        // depth-2 store: IR = %0 = o.f; %0.v = src()
            leak(o);
        }
        void leak(L0 p) { sink(p.f.v); }
    }

    // Depth-2 field store, then precise intraprocedural read of the same deep field.
    final static class PositiveDepth2Precise extends DeepFieldStoreFn {
        @Override public void entrypoint() {
            L0 o = new L0();
            o.f = new L1();
            o.f.v = src();
            sink(o.f.v);
        }
    }
}
