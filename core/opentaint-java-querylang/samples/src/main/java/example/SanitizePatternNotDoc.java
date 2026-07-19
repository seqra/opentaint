package example;

import base.RuleSample;
import base.RuleSet;
import base.TaintRuleFalsePositive;

/**
 * Doc validation: documents the current argument-position restriction: a
 * pattern-not event that uses the tracked value only as a call argument
 * (static-call sanitize) does not yet anchor the exclusion. See
 * ReceiverSanitizePatternNotDoc for the working receiver-shaped form.
 */
@RuleSet("example/SanitizePatternNotDoc.yaml")
public abstract class SanitizePatternNotDoc implements RuleSample {

    static Object decode(Object o) { return o; }
    static Object sanitize(Object o) { return o; }
    static void consume(Object o) {}

    static class Positive extends SanitizePatternNotDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            consume(r);
        }
    }

    @TaintRuleFalsePositive("negative clauses do not anchor on argument-position events")
    static class Negative extends SanitizePatternNotDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            r = sanitize(r);
            consume(r);
        }
    }
}
