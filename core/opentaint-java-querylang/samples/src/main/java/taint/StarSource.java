package taint;

import base.RuleSample;
import base.RuleSet;

@RuleSet("taint/StarSource.yaml")
public abstract class StarSource implements RuleSample {
    String src() { return "tainted"; }
    void sink(Box b) {}

    static final class Box {
        private String value;
        String getValue() { return value; }
        void setValue(String value) { this.value = value; }
    }

    // Positive: a source-tainted value flows through an interprocedural setter
    // into the object's field; the $Y* sink observes the tainted field.
    final static class PositiveFieldFlow extends StarSource {
        @Override public void entrypoint() {
            String data = src();
            Box b = new Box();
            b.setValue(data);       // taints b.value (field) via setter
            sink(b);                // $Y* sink fires on tainted field
        }
    }

    // Negative: the field is never tainted.
    final static class NegativeCleanField extends StarSource {
        @Override public void entrypoint() {
            String data = src();
            Box b = new Box();
            b.setValue("safe");
            sink(b);
            System.out.println(data);
        }
    }
}
