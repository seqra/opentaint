package test.samples;

public class DeepCleanSummarySample {
    public static class Box {
        public String f;
    }

    public static class Pair {
        public Box raw;
        public Box val;
    }

    public void clean(Box b) { }
    public void sink(String data) { }

    Pair wrap(Box b) {
        Pair p = new Pair();
        p.raw = b;
        clean(b);
        p.val = b;
        return p;
    }

    public void cleanedFlow(Box b) {
        Pair p = wrap(b);
        sink(p.val.f);
    }

    public void uncleanedFlow(Box b) {
        Pair p = wrap(b);
        sink(p.raw.f);
    }

    Pair wrapConditional(Box b, boolean flag) {
        Pair p = new Pair();
        if (flag) {
            clean(b);
        }
        p.val = b;
        return p;
    }

    public void conditionalCleanFlow(Box b, boolean flag) {
        Pair p = wrapConditional(b, flag);
        sink(p.val.f);
    }

    Box wrapCleanOnly(Box b) {
        clean(b);
        return b;
    }

    public void cleanOnlyFlow(Box b) {
        Box r = wrapCleanOnly(b);
        sink(r.f);
    }
}
