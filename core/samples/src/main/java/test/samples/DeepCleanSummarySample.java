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

    // The whole cleaned flow inside ONE summarized helper: clean, then read, then return the
    // read value. The claim never has to reach the entry point's own fact -- it must be
    // effective inside the helper's summary computation.
    String helperCleanThenRead(Box b) {
        clean(b);
        return b.f;
    }

    public void helperCleanReadFlow(Box b) {
        sink(helperCleanThenRead(b));
    }

    // Non-vacuity control for the same frame shape: no clean, the read must report.
    String helperReadOnly(Box b) {
        return b.f;
    }

    public void helperReadFlow(Box b) {
        sink(helperReadOnly(b));
    }

    // Same, with the clean one summary level deeper.
    String helperNestedCleanThenRead(Box b) {
        Box c = wrapCleanOnly(b);
        return c.f;
    }

    public void helperNestedCleanReadFlow(Box b) {
        sink(helperNestedCleanThenRead(b));
    }

    public void sinkBox(Box b) { }

    public void boxCleanedFlow(Box b) {
        Pair p = wrap(b);
        sinkBox(p.val);
    }

    public void boxUncleanedFlow(Box b) {
        Pair p = wrap(b);
        sinkBox(p.raw);
    }

    public static class Leaf {
        public String k;
    }

    public static class Node {
        public Leaf f;
    }

    public static class NodePair {
        public Node raw;
        public Node val;
    }

    public void cleanNode(Node b) { }

    NodePair wrapNode(Node b) {
        NodePair p = new NodePair();
        p.raw = b;
        cleanNode(b);
        p.val = b;
        return p;
    }

    public void nodeCleanedFlow(Node b) {
        NodePair p = wrapNode(b);
        sink(p.val.f.k);
    }

    public void nodeUncleanedFlow(Node b) {
        NodePair p = wrapNode(b);
        sink(p.raw.f.k);
    }

    // Clean plus a depth-2 constant store inside one summarized helper; the object is
    // returned and the caller reads the stored path.
    Node cleanThenAssignLeaf(Node b) {
        cleanNode(b);
        b.f.k = "safe";
        return b;
    }

    public void nodeCleanAssignFlow(Node b) {
        Node r = cleanThenAssignLeaf(b);
        sink(r.f.k);
    }
}
