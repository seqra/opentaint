package example;

import base.RuleSample;
import base.RuleSet;

/**
 * Doc validation: pattern-not-inside whose excluded event is the
 * self-sanitizing reassignment does not anchor the exclusion — the tracked
 * value sits in argument position of the static call. The identical event
 * matches positively (SanitizeEventSanityDoc), and the receiver-position
 * counterpart excludes (ReceiverSanitizePatternNotDoc).
 */
@RuleSet("example/SanitizeNotInsideDoc.yaml")
public abstract class SanitizeNotInsideDoc implements RuleSample {

    static Object decode(Object o) { return o; }
    static Object sanitize(Object o) { return o; }
    static void consume(Object o) {}

    static class Positive extends SanitizeNotInsideDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            consume(r);
        }
    }

    static class PositiveNotYetExcluded extends SanitizeNotInsideDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            r = sanitize(r);
            consume(r);
        }
    }
}
