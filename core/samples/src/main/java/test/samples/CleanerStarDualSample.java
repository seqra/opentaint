package test.samples;

public class CleanerStarDualSample {
    public static class Node {
        public Node k;
        public Object value;
    }

    public void applyPlainClean(Node value) { }

    public void inlineCleanerThenFieldSink(Node value) {
        applyPlainClean(value);
        fieldSink(value.k);
    }

    public void calleeCleanerThenFieldSink(Node value) {
        cleanAndSink(value);
    }

    private void cleanAndSink(Node value) {
        applyPlainClean(value);
        fieldSink(value.k);
    }

    public void nestedStoreThenCleanerThenAnySink(Node value) {
        value.k = new Node();
        value.k.value = source();
        applyPlainClean(value);
        anySink(value);
    }

    public Object source() { return null; }

    public void fieldSink(Object value) { }

    public void anySink(Object value) { }
}
