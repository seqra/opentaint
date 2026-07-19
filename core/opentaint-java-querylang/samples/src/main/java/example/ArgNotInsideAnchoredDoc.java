package example;

import base.RuleSample;
import base.RuleSet;

/**
 * Doc validation: argument-position pattern-not-inside does not anchor even
 * with a satisfiable containment — the producer lives in pattern-inside and
 * the main pattern is the single consume event, so the excluded context can
 * enclose the match, yet the exclusion still has no effect. Contrast with
 * ReceiverNotInsideSpanDoc, where a receiver-position exclusion works even
 * when the context cannot contain the producing event.
 */
@RuleSet("example/ArgNotInsideAnchoredDoc.yaml")
public abstract class ArgNotInsideAnchoredDoc implements RuleSample {

    static Object decode(Object o) { return o; }
    static int checksum;

    static void check(Object o) { checksum += o.hashCode(); }
    static void consume(Object o) {}

    static class Positive extends ArgNotInsideAnchoredDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            consume(r);
        }
    }

    static class PositiveNotYetExcluded extends ArgNotInsideAnchoredDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            check(r);
            consume(r);
        }
    }
}
