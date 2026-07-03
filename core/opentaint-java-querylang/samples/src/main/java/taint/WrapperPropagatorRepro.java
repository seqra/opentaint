package taint;

import base.RuleSample;
import base.RuleSet;

/**
 * Repro for the residual #2 gap: a pattern-propagator that carries taint from a
 * constructor argument into the constructed wrapper object
 * (`$W = new Wrapper($SPEC)`) fires when $SPEC is a plain tainted variable, but
 * not when $SPEC is a string concatenation. Mirrors the path-traversal FN where
 * `new java.net.URL("file:///..." + resource)` -> HttpResponses.staticResource(url)
 * is missed while `new URL(url)` in a `URL[]` is detected.
 *
 * Both positives must be reported. If PositiveConcat is missed while PositiveDirect
 * is found, the propagator does not see taint on a concatenated argument.
 */
@RuleSet("taint/WrapperPropagatorRepro.yaml")
public abstract class WrapperPropagatorRepro implements RuleSample {

    String src() {
        return "tainted";
    }

    void sink(Object data) {
    }

    static final class Wrapper {
        private final String v;

        Wrapper(String v) {
            this.v = v;
        }
    }

    static final class PositiveDirect extends WrapperPropagatorRepro {
        @Override
        public void entrypoint() {
            String data = src();
            Wrapper w = new Wrapper(data);
            sink(w);
        }
    }

    static final class PositiveConcat extends WrapperPropagatorRepro {
        @Override
        public void entrypoint() {
            String data = src();
            Wrapper w = new Wrapper("prefix/" + data);
            sink(w);
        }
    }
}
