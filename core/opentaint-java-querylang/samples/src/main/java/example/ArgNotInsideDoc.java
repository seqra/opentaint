package example;

import base.RuleSample;
import base.RuleSet;

/**
 * Doc validation: pattern-not-inside whose excluded event uses the
 * positively produced value in argument position does not anchor the
 * exclusion — while the identical event matches positively (see
 * ArgEventSanityDoc).
 */
@RuleSet("example/ArgNotInsideDoc.yaml")
public abstract class ArgNotInsideDoc implements RuleSample {

    static Object decode(Object o) { return o; }
    static int checksum;

    static void check(Object o) { checksum += o.hashCode(); }
    static void consume(Object o) {}

    static class Positive extends ArgNotInsideDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            consume(r);
        }
    }

    static class PositiveNotYetExcluded extends ArgNotInsideDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            check(r);
            consume(r);
        }
    }
}
