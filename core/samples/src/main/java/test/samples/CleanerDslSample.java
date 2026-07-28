package test.samples;

public class CleanerDslSample {
    public static class Node {
        public Level2 k;
        public Node child;
    }

    public static class Level2 {
        public Level3 k;
        public Node p;
    }

    public static class Level3 {
        public Level4 k;
    }

    public static class Level4 {
        public Level5 k;
    }

    public static class Level5 {
        public Level6 k;
    }

    public static class Level6 {
    }

    public Node sourcePlain() {
        return new Node();
    }

    public Node sourceAny() {
        return new Node();
    }

    public Node cleanPlain(Node value) {
        return value;
    }

    public Node cleanAny(Node value) {
        return value;
    }

    public void applyPlainClean(Node value) { }

    public void applyAnyClean(Node value) { }

    public void plainMarks1(Node plainCleaned, Node anyCleaned) {
        plainPlain(plainCleaned);
        plainAny(anyCleaned);
    }

    public void plainMarks2(Node plainCleaned, Node anyCleaned) {
        plainPlain(plainCleaned);
        plainAny(anyCleaned);
    }

    public void plainMarks3(Node plainCleaned, Node anyCleaned) {
        plainPlain(plainCleaned);
        plainAny(anyCleaned);
    }

    public void plainMarks4(Node plainCleaned, Node anyCleaned) {
        plainPlain(plainCleaned);
        plainAny(anyCleaned);
    }

    public void plainMarks5(Node plainCleaned, Node anyCleaned) {
        plainPlain(plainCleaned);
        plainAny(anyCleaned);
    }

    public void anyMarks1(Node plainCleaned, Node anyCleaned) {
        anyPlain(plainCleaned);
        anyAny(anyCleaned);
    }

    public void anyMarks2(Node plainCleaned, Node anyCleaned) {
        anyPlain(plainCleaned);
        anyAny(anyCleaned);
    }

    public void anyMarks3(Node plainCleaned, Node anyCleaned) {
        anyPlain(plainCleaned);
        anyAny(anyCleaned);
    }

    public void anyMarks4(Node plainCleaned, Node anyCleaned) {
        anyPlain(plainCleaned);
        anyAny(anyCleaned);
    }

    public void anyMarks5(Node plainCleaned, Node anyCleaned) {
        anyPlain(plainCleaned);
        anyAny(anyCleaned);
    }

    public void cleanMarks1(Node value) {
        applyAnyClean(value);
        markSelectiveSink(value);
    }

    public void cleanMarks2(Node value) {
        applyAnyClean(value);
        markSelectiveSink(value);
    }

    public void cleanMarks3(Node value) {
        applyAnyClean(value);
        markSelectiveSink(value);
    }

    public void cleanMarks4(Node value) {
        applyAnyClean(value);
        markSelectiveSink(value);
    }

    public void cleanMarks5(Node value) {
        applyAnyClean(value);
        markSelectiveSink(value);
    }

    // Four source/cleaner pairs. Each pair checks both sink forms at field depth 0..5 and then
    // sends the depth-1 field through helper stacks 1..5.

    private void plainPlain(Node value) {
        applyPlainClean(value);
        sinkPlainPlainPlainDepth0(value);
        sinkPlainPlainAnyDepth0(value);
        sinkPlainPlainPlainDepth1(value.k);
        sinkPlainPlainAnyDepth1(value.k);
        sinkPlainPlainPlainDepth2(value.k.k);
        sinkPlainPlainAnyDepth2(value.k.k);
        sinkPlainPlainPlainDepth3(value.k.k.k);
        sinkPlainPlainAnyDepth3(value.k.k.k);
        sinkPlainPlainPlainDepth4(value.k.k.k.k);
        sinkPlainPlainAnyDepth4(value.k.k.k.k);
        sinkPlainPlainPlainDepth5(value.k.k.k.k.k);
        sinkPlainPlainAnyDepth5(value.k.k.k.k.k);
        plainPlainStackDepth1(value);
    }

    private void plainPlainStackDepth1(Node value) {
        sinkPlainPlainPlainStackDepth1(value.k);
        sinkPlainPlainAnyStackDepth1(value.k);
        plainPlainStackDepth2(value);
    }

    private void plainPlainStackDepth2(Node value) {
        sinkPlainPlainPlainStackDepth2(value.k);
        sinkPlainPlainAnyStackDepth2(value.k);
        plainPlainStackDepth3(value);
    }

    private void plainPlainStackDepth3(Node value) {
        sinkPlainPlainPlainStackDepth3(value.k);
        sinkPlainPlainAnyStackDepth3(value.k);
        plainPlainStackDepth4(value);
    }

    private void plainPlainStackDepth4(Node value) {
        sinkPlainPlainPlainStackDepth4(value.k);
        sinkPlainPlainAnyStackDepth4(value.k);
        plainPlainStackDepth5(value);
    }

    private void plainPlainStackDepth5(Node value) {
        sinkPlainPlainPlainStackDepth5(value.k);
        sinkPlainPlainAnyStackDepth5(value.k);
    }

    private void plainAny(Node value) {
        applyAnyClean(value);
        sinkPlainAnyPlainDepth0(value);
        sinkPlainAnyAnyDepth0(value);
        sinkPlainAnyPlainDepth1(value.k);
        sinkPlainAnyAnyDepth1(value.k);
        sinkPlainAnyPlainDepth2(value.k.k);
        sinkPlainAnyAnyDepth2(value.k.k);
        sinkPlainAnyPlainDepth3(value.k.k.k);
        sinkPlainAnyAnyDepth3(value.k.k.k);
        sinkPlainAnyPlainDepth4(value.k.k.k.k);
        sinkPlainAnyAnyDepth4(value.k.k.k.k);
        sinkPlainAnyPlainDepth5(value.k.k.k.k.k);
        sinkPlainAnyAnyDepth5(value.k.k.k.k.k);
        plainAnyStackDepth1(value);
    }

    private void plainAnyStackDepth1(Node value) {
        sinkPlainAnyPlainStackDepth1(value.k);
        sinkPlainAnyAnyStackDepth1(value.k);
        plainAnyStackDepth2(value);
    }

    private void plainAnyStackDepth2(Node value) {
        sinkPlainAnyPlainStackDepth2(value.k);
        sinkPlainAnyAnyStackDepth2(value.k);
        plainAnyStackDepth3(value);
    }

    private void plainAnyStackDepth3(Node value) {
        sinkPlainAnyPlainStackDepth3(value.k);
        sinkPlainAnyAnyStackDepth3(value.k);
        plainAnyStackDepth4(value);
    }

    private void plainAnyStackDepth4(Node value) {
        sinkPlainAnyPlainStackDepth4(value.k);
        sinkPlainAnyAnyStackDepth4(value.k);
        plainAnyStackDepth5(value);
    }

    private void plainAnyStackDepth5(Node value) {
        sinkPlainAnyPlainStackDepth5(value.k);
        sinkPlainAnyAnyStackDepth5(value.k);
    }

    private void anyPlain(Node value) {
        applyPlainClean(value);
        sinkAnyPlainPlainDepth0(value);
        sinkAnyPlainAnyDepth0(value);
        sinkAnyPlainPlainDepth1(value.k);
        sinkAnyPlainAnyDepth1(value.k);
        sinkAnyPlainPlainDepth2(value.k.k);
        sinkAnyPlainAnyDepth2(value.k.k);
        sinkAnyPlainPlainDepth3(value.k.k.k);
        sinkAnyPlainAnyDepth3(value.k.k.k);
        sinkAnyPlainPlainDepth4(value.k.k.k.k);
        sinkAnyPlainAnyDepth4(value.k.k.k.k);
        sinkAnyPlainPlainDepth5(value.k.k.k.k.k);
        sinkAnyPlainAnyDepth5(value.k.k.k.k.k);
        anyPlainStackDepth1(value);
    }

    private void anyPlainStackDepth1(Node value) {
        sinkAnyPlainPlainStackDepth1(value.k);
        sinkAnyPlainAnyStackDepth1(value.k);
        anyPlainStackDepth2(value);
    }

    private void anyPlainStackDepth2(Node value) {
        sinkAnyPlainPlainStackDepth2(value.k);
        sinkAnyPlainAnyStackDepth2(value.k);
        anyPlainStackDepth3(value);
    }

    private void anyPlainStackDepth3(Node value) {
        sinkAnyPlainPlainStackDepth3(value.k);
        sinkAnyPlainAnyStackDepth3(value.k);
        anyPlainStackDepth4(value);
    }

    private void anyPlainStackDepth4(Node value) {
        sinkAnyPlainPlainStackDepth4(value.k);
        sinkAnyPlainAnyStackDepth4(value.k);
        anyPlainStackDepth5(value);
    }

    private void anyPlainStackDepth5(Node value) {
        sinkAnyPlainPlainStackDepth5(value.k);
        sinkAnyPlainAnyStackDepth5(value.k);
    }

    private void anyAny(Node value) {
        applyAnyClean(value);
        sinkAnyAnyPlainDepth0(value);
        sinkAnyAnyAnyDepth0(value);
        sinkAnyAnyPlainDepth1(value.k);
        sinkAnyAnyAnyDepth1(value.k);
        sinkAnyAnyPlainDepth2(value.k.k);
        sinkAnyAnyAnyDepth2(value.k.k);
        sinkAnyAnyPlainDepth3(value.k.k.k);
        sinkAnyAnyAnyDepth3(value.k.k.k);
        sinkAnyAnyPlainDepth4(value.k.k.k.k);
        sinkAnyAnyAnyDepth4(value.k.k.k.k);
        sinkAnyAnyPlainDepth5(value.k.k.k.k.k);
        sinkAnyAnyAnyDepth5(value.k.k.k.k.k);
        anyAnyStackDepth1(value);
    }

    private void anyAnyStackDepth1(Node value) {
        sinkAnyAnyPlainStackDepth1(value.k);
        sinkAnyAnyAnyStackDepth1(value.k);
        anyAnyStackDepth2(value);
    }

    private void anyAnyStackDepth2(Node value) {
        sinkAnyAnyPlainStackDepth2(value.k);
        sinkAnyAnyAnyStackDepth2(value.k);
        anyAnyStackDepth3(value);
    }

    private void anyAnyStackDepth3(Node value) {
        sinkAnyAnyPlainStackDepth3(value.k);
        sinkAnyAnyAnyStackDepth3(value.k);
        anyAnyStackDepth4(value);
    }

    private void anyAnyStackDepth4(Node value) {
        sinkAnyAnyPlainStackDepth4(value.k);
        sinkAnyAnyAnyStackDepth4(value.k);
        anyAnyStackDepth5(value);
    }

    private void anyAnyStackDepth5(Node value) {
        sinkAnyAnyPlainStackDepth5(value.k);
        sinkAnyAnyAnyStackDepth5(value.k);
    }

    // Direct translations of the field-store, nested-cleaner, helper-source, helper-sink, and
    // branch-join examples. These use method sources rather than entry-point sources.

    public void fieldStoreExamples() {
        Node plainRoot = new Node();
        plainRoot.child = sourcePlain();
        Node plainCleaned = cleanPlain(plainRoot);
        fieldStorePlainSink(plainCleaned);
        fieldStoreAnySink(plainCleaned);

        Node anyCleaned = cleanAny(plainRoot);
        fieldStoreAfterAnyCleanSink(anyCleaned);
    }

    public void nestedHelperCleanerExample() {
        Node value = new Node();
        value.k.p = sourceAny();
        Node cleaned = helperAnyClean(value);
        nestedHelperAnySink(cleaned);
    }

    private Node helperAnyClean(Node value) {
        value.k.p = cleanAny(value.k.p);
        return value;
    }

    public void helperSourceAndCleanerExample() {
        Node value = new Node();
        value.child = helperSource();
        Node cleaned = cleanAny(value);
        helperSourceAnySink(cleaned);
    }

    private Node helperSource() {
        return sourcePlain();
    }

    public void helperSinkExample() {
        Node value = new Node();
        value.child = helperSource();
        Node cleaned = cleanAny(value);
        helperAnySink(cleaned);
    }

    private void helperAnySink(Node value) {
        helperSinkAnySink(value.child);
    }

    public void conditionalExample(boolean flag) {
        Node a = sourceA();
        Node x = sourceX();
        Node b;
        Node y;
        if (flag) {
            b = cleanA(a);
            y = x;
        } else {
            b = a;
            y = cleanX(x);
        }
        sinkA(b);
        sinkX(y);
    }

    public Node sourceA() {
        return new Node();
    }

    public Node sourceX() {
        return new Node();
    }

    public Node cleanA(Node value) {
        return value;
    }

    public Node cleanX(Node value) {
        return value;
    }

    // Every matrix endpoint has a distinct method so its rule id identifies one exact coordinate.

    public void sinkPlainPlainPlainDepth0(Object value) { }
    public void sinkPlainPlainPlainDepth1(Object value) { }
    public void sinkPlainPlainPlainDepth2(Object value) { }
    public void sinkPlainPlainPlainDepth3(Object value) { }
    public void sinkPlainPlainPlainDepth4(Object value) { }
    public void sinkPlainPlainPlainDepth5(Object value) { }
    public void sinkPlainPlainAnyDepth0(Object value) { }
    public void sinkPlainPlainAnyDepth1(Object value) { }
    public void sinkPlainPlainAnyDepth2(Object value) { }
    public void sinkPlainPlainAnyDepth3(Object value) { }
    public void sinkPlainPlainAnyDepth4(Object value) { }
    public void sinkPlainPlainAnyDepth5(Object value) { }
    public void sinkPlainAnyPlainDepth0(Object value) { }
    public void sinkPlainAnyPlainDepth1(Object value) { }
    public void sinkPlainAnyPlainDepth2(Object value) { }
    public void sinkPlainAnyPlainDepth3(Object value) { }
    public void sinkPlainAnyPlainDepth4(Object value) { }
    public void sinkPlainAnyPlainDepth5(Object value) { }
    public void sinkPlainAnyAnyDepth0(Object value) { }
    public void sinkPlainAnyAnyDepth1(Object value) { }
    public void sinkPlainAnyAnyDepth2(Object value) { }
    public void sinkPlainAnyAnyDepth3(Object value) { }
    public void sinkPlainAnyAnyDepth4(Object value) { }
    public void sinkPlainAnyAnyDepth5(Object value) { }
    public void sinkAnyPlainPlainDepth0(Object value) { }
    public void sinkAnyPlainPlainDepth1(Object value) { }
    public void sinkAnyPlainPlainDepth2(Object value) { }
    public void sinkAnyPlainPlainDepth3(Object value) { }
    public void sinkAnyPlainPlainDepth4(Object value) { }
    public void sinkAnyPlainPlainDepth5(Object value) { }
    public void sinkAnyPlainAnyDepth0(Object value) { }
    public void sinkAnyPlainAnyDepth1(Object value) { }
    public void sinkAnyPlainAnyDepth2(Object value) { }
    public void sinkAnyPlainAnyDepth3(Object value) { }
    public void sinkAnyPlainAnyDepth4(Object value) { }
    public void sinkAnyPlainAnyDepth5(Object value) { }
    public void sinkAnyAnyPlainDepth0(Object value) { }
    public void sinkAnyAnyPlainDepth1(Object value) { }
    public void sinkAnyAnyPlainDepth2(Object value) { }
    public void sinkAnyAnyPlainDepth3(Object value) { }
    public void sinkAnyAnyPlainDepth4(Object value) { }
    public void sinkAnyAnyPlainDepth5(Object value) { }
    public void sinkAnyAnyAnyDepth0(Object value) { }
    public void sinkAnyAnyAnyDepth1(Object value) { }
    public void sinkAnyAnyAnyDepth2(Object value) { }
    public void sinkAnyAnyAnyDepth3(Object value) { }
    public void sinkAnyAnyAnyDepth4(Object value) { }
    public void sinkAnyAnyAnyDepth5(Object value) { }

    public void sinkPlainPlainPlainStackDepth1(Object value) { }
    public void sinkPlainPlainPlainStackDepth2(Object value) { }
    public void sinkPlainPlainPlainStackDepth3(Object value) { }
    public void sinkPlainPlainPlainStackDepth4(Object value) { }
    public void sinkPlainPlainPlainStackDepth5(Object value) { }
    public void sinkPlainPlainAnyStackDepth1(Object value) { }
    public void sinkPlainPlainAnyStackDepth2(Object value) { }
    public void sinkPlainPlainAnyStackDepth3(Object value) { }
    public void sinkPlainPlainAnyStackDepth4(Object value) { }
    public void sinkPlainPlainAnyStackDepth5(Object value) { }
    public void sinkPlainAnyPlainStackDepth1(Object value) { }
    public void sinkPlainAnyPlainStackDepth2(Object value) { }
    public void sinkPlainAnyPlainStackDepth3(Object value) { }
    public void sinkPlainAnyPlainStackDepth4(Object value) { }
    public void sinkPlainAnyPlainStackDepth5(Object value) { }
    public void sinkPlainAnyAnyStackDepth1(Object value) { }
    public void sinkPlainAnyAnyStackDepth2(Object value) { }
    public void sinkPlainAnyAnyStackDepth3(Object value) { }
    public void sinkPlainAnyAnyStackDepth4(Object value) { }
    public void sinkPlainAnyAnyStackDepth5(Object value) { }
    public void sinkAnyPlainPlainStackDepth1(Object value) { }
    public void sinkAnyPlainPlainStackDepth2(Object value) { }
    public void sinkAnyPlainPlainStackDepth3(Object value) { }
    public void sinkAnyPlainPlainStackDepth4(Object value) { }
    public void sinkAnyPlainPlainStackDepth5(Object value) { }
    public void sinkAnyPlainAnyStackDepth1(Object value) { }
    public void sinkAnyPlainAnyStackDepth2(Object value) { }
    public void sinkAnyPlainAnyStackDepth3(Object value) { }
    public void sinkAnyPlainAnyStackDepth4(Object value) { }
    public void sinkAnyPlainAnyStackDepth5(Object value) { }
    public void sinkAnyAnyPlainStackDepth1(Object value) { }
    public void sinkAnyAnyPlainStackDepth2(Object value) { }
    public void sinkAnyAnyPlainStackDepth3(Object value) { }
    public void sinkAnyAnyPlainStackDepth4(Object value) { }
    public void sinkAnyAnyPlainStackDepth5(Object value) { }
    public void sinkAnyAnyAnyStackDepth1(Object value) { }
    public void sinkAnyAnyAnyStackDepth2(Object value) { }
    public void sinkAnyAnyAnyStackDepth3(Object value) { }
    public void sinkAnyAnyAnyStackDepth4(Object value) { }
    public void sinkAnyAnyAnyStackDepth5(Object value) { }

    public void fieldStorePlainSink(Node value) { }
    public void fieldStoreAnySink(Node value) { }
    public void fieldStoreAfterAnyCleanSink(Node value) { }
    public void nestedHelperAnySink(Node value) { }
    public void helperSourceAnySink(Node value) { }
    public void helperSinkAnySink(Node value) { }
    public void markSelectiveSink(Node value) { }
    public void sinkA(Object value) { }
    public void sinkX(Object value) { }
}
