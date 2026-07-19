package example;

import base.RuleSample;
import base.RuleSet;

/**
 * Doc validation: full-form pattern-not whose added event uses the produced
 * value in argument position does not anchor the exclusion — while the
 * identical event matches positively (see ArgEventSanityDoc).
 */
@RuleSet("example/ArgFullPatternNotDoc.yaml")
public abstract class ArgFullPatternNotDoc implements RuleSample {

    static Object decode(Object o) { return o; }
    static int checksum;

    static void check(Object o) { checksum += o.hashCode(); }
    static void consume(Object o) {}

    static class Positive extends ArgFullPatternNotDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            consume(r);
        }
    }

    static class Negative extends ArgFullPatternNotDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            check(r);
            consume(r);
        }
    }
}
