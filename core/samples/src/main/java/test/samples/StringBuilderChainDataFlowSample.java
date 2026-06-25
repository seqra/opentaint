package test.samples;

/**
 * Reproduces the chained-{@code StringBuilder.append(...).append(...)} taint loss from issue.md.
 *
 * In every flow {@code b = source()} is the tainted value and the separator/literal appends are
 * untrusted. The sink reads a {@code toString()} of the receiver indicated in each method. Whether the
 * sink should fire is stated per-method; the engine drops the taint when the tainted value is the
 * non-first append of a chain whose result is discarded and the original receiver is read back later.
 */
public class StringBuilderChainDataFlowSample {

    // Two appends on the original receiver, chain result never formed. FIRES (correct).
    public void unchained() {
        String b = source();
        StringBuilder sb = new StringBuilder();
        sb.append("/");
        sb.append(b);
        sink(sb.toString());
    }

    // Tainted b is the FIRST append of the chain; arg(0) -> this lands on the original sb. FIRES (correct).
    public void chainTaintFirst() {
        String b = source();
        StringBuilder sb = new StringBuilder();
        sb.append(b).append("x");
        sink(sb.toString());
    }

    // Tainted b is the SECOND append of a discarded chain; sink reads the ORIGINAL sb.
    // Should FIRE (append returns this at runtime, sb is mutated) but the engine drops it.
    public void chainedAppend() {
        String b = source();
        StringBuilder sb = new StringBuilder();
        sb.append("/").append(b);
        sink(sb.toString());
    }

    // Intermediate return is named r; r.append(b) mutates the tracked intermediate, sink reads ORIGINAL sb.
    // Should FIRE (r and sb are the same object at runtime) but the engine drops it.
    public void namedReturn() {
        String b = source();
        StringBuilder sb = new StringBuilder();
        StringBuilder r = sb.append("x");
        r.append(b);
        sink(sb.toString());
    }

    // Same chain, but the sink reads the chain-end r that actually received b. FIRES (correct).
    public void sinkChainResult() {
        String b = source();
        StringBuilder sb = new StringBuilder();
        StringBuilder r = sb.append("x").append(b);
        sink(r.toString());
    }

    public String source() { return "tainted"; }
    public void sink(String data) { }
}
