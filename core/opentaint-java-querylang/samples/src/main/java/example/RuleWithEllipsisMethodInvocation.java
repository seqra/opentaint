package example;

import base.RuleSample;
import base.RuleSet;

@RuleSet("example/RuleWithEllipsisMethodInvocation.yaml")
public abstract class RuleWithEllipsisMethodInvocation implements RuleSample {
    Inner src() {
        return new Inner(new Inner2());
    }

    void sink(String data) {}

    final static class PositiveOneCall extends RuleWithEllipsisMethodInvocation {
        @Override
        public void entrypoint() {
            Inner data = src();
            String str = data.getInner().toString();
            sink(str);
        }
    }

    final static class PositiveZeroCalls extends RuleWithEllipsisMethodInvocation {
        @Override
        public void entrypoint() {
            Inner data = src();
            String str = data.toString();
            sink(str);
        }
    }

    final static class NegativeTwoCalls extends RuleWithEllipsisMethodInvocation {
        @Override
        public void entrypoint() {
            Inner data = src();
            String str = data.getInner().getObjGood().toString();
            sink(str);
        }
    }

    private static final class Inner2 {
        final private Object obj = new Object();

        public Object getObjGood() {
            return obj;
        }
    }

    static final private class Inner {
        final private Inner2 obj;

        public Inner(Inner2 obj) {
            this.obj = obj;
        }

        public Inner2 getInner() {
            return obj;
        }
    }
}

