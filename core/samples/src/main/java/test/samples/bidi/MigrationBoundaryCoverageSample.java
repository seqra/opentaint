package test.samples.bidi;

/** Small native controls for entry-source cleanup and static report routing. */
public class MigrationBoundaryCoverageSample {
    public static class Node { public Node next; }
    public static Object shared;
    public static void clean(Node x) { }
    public static void sink(Object x) { }

    public static void shallowAfterRootClean(Node x) {
        clean(x);
        sink(x.next);
    }

    public static void deepAfterRootClean(Node x) {
        clean(x);
        sink(x.next.next);
    }

    public static void staticAfterEntrySource(Object x) {
        shared = x;
        sink(shared);
    }

    public static void rootWithClear() {
        staticAfterEntrySource(null);
        clearShared();
    }

    public static void clearShared() { shared = null; }
}
