package example;

import base.RuleSample;
import base.RuleSet;

@RuleSet("example/RuleNoPrimitive.yaml")
public abstract class RuleNoPrimitive implements RuleSample {
    int src() {
        return 0;
    }

    void sink(int data) {

    }

    final static class NegativeSimple extends RuleNoPrimitive {
        @Override
        public void entrypoint() {
            int data = src();
            sink(data);
        }
    }
}
