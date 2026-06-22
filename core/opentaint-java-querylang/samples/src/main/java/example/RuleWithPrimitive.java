package example;

import base.RuleSample;
import base.RuleSet;

@RuleSet("example/RuleWithPrimitive.yaml")
public abstract class RuleWithPrimitive implements RuleSample {
    int src() {
        return 0;
    }

    void sink(int data) {

    }

    final static class PositiveSimple extends RuleWithPrimitive {
        @Override
        public void entrypoint() {
            int data = src();
            sink(data);
        }
    }
}
