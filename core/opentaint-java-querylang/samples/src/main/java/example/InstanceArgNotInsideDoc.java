package example;

import base.RuleSample;
import base.RuleSet;

/**
 * Doc validation: pattern-not-inside whose excluded event is an instance
 * call taking the produced value as an argument (anonymous receiver), in
 * the anchored shape: producer in pattern-inside, single-event main
 * pattern.
 */
@RuleSet("example/InstanceArgNotInsideDoc.yaml")
public abstract class InstanceArgNotInsideDoc implements RuleSample {

    static class Aux {
        int state;
        void verify(Object o) { state += o.hashCode(); }
    }

    static Object decode(Object o) { return o; }
    static void consume(Object o) {}

    static class Positive extends InstanceArgNotInsideDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            consume(r);
        }
    }

    static class Negative extends InstanceArgNotInsideDoc {
        @Override
        public void entrypoint() {
            Object r = decode("x");
            new Aux().verify(r);
            consume(r);
        }
    }
}
