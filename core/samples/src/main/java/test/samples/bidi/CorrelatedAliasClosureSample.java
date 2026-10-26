package test.samples.bidi;

public class CorrelatedAliasClosureSample {
    public static class Box {
        public Object value;
        public Box next;
    }

    public static Object source() { return new Object(); }
    public static void mark(Object value) { }
    public static void identity(Object value) { }
    public static void sink(Object value) { }

    public static void aliasAfterMark() {
        Object p = source();
        Object q = p;
        identity(p);
        sink(q);
    }

    public static void markAfterAlias() {
        Object p = new Object();
        Object q = p;
        mark(p);
        identity(p);
        sink(q);
    }

    public static void fieldAliasAfterMark() {
        Box p = new Box();
        p.value = source();
        Box q = p;
        identity(p);
        sink(q.value);
    }

    public static void fieldMarkAfterAlias() {
        Box p = new Box();
        Box q = p;
        p.value = source();
        identity(p);
        sink(q.value);
    }

    public static void laterDemandedAlias(Box p) {
        Box q = p;
        identity(p);
        sink(q.next.value);
    }
}
