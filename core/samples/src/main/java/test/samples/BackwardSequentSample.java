package test.samples;

public class BackwardSequentSample {
    public static class Box {
        public String f;
        public String g;
    }

    public static class Holder {
        public Box box;
    }

    public static class Node {
        public Node next;
        public String val;
    }

    public static String STATIC_FIELD;
    public static String SOURCE_FIELD = "source";

    public void simpleAssign(String p) {
        String a = p;
        String b = a;
        sink(b);
    }

    public void simpleAssignNegative(String p, String q) {
        String a = q;
        sink(a);
    }

    public void overwriteLocal(String p) {
        String a = p;
        a = "clean";
        sink(a);
    }

    public void castFlow(String p) {
        Object o = p;
        String s = (String) o;
        sink(s);
    }

    public void fieldWriteRead(String p) {
        Box b = new Box();
        b.f = p;
        sink(b.f);
    }

    public void fieldOverwrite(String p) {
        Box b = new Box();
        b.f = p;
        b.f = "clean";
        sink(b.f);
    }

    public void otherField(String p) {
        Box b = new Box();
        b.f = p;
        sink(b.g);
    }

    public void fieldKeepOther(String p) {
        Box b = new Box();
        b.f = p;
        b.g = "clean";
        sink(b.f);
    }

    public void fieldAlias(String p) {
        Box b = new Box();
        Holder h = new Holder();
        h.box = b;
        Box b2 = h.box;
        b2.f = p;
        sink(b.f);
    }

    public void fieldNoAlias(String p) {
        Box b = new Box();
        Holder h = new Holder();
        h.box = new Box();
        Box b2 = h.box;
        b2.f = p;
        sink(b.f);
    }

    public void arrayAlias(String p) {
        String[] arr = new String[2];
        Object[] holder = new Object[1];
        holder[0] = arr;
        String[] arr2 = (String[]) holder[0];
        arr2[0] = p;
        sink(arr[0]);
    }

    public void arrayWriteRead(String p) {
        String[] arr = new String[2];
        arr[0] = p;
        sink(arr[0]);
    }

    public void arrayWeakUpdate(String p) {
        String[] arr = new String[2];
        arr[0] = p;
        arr[1] = "clean";
        sink(arr[0]);
    }

    public void arrayNegative(String p) {
        String[] arr = new String[2];
        arr[0] = "clean";
        sink(arr[0]);
    }

    public void staticWriteRead(String p) {
        STATIC_FIELD = p;
        String a = STATIC_FIELD;
        sink(a);
    }

    public void staticOverwrite(String p) {
        STATIC_FIELD = p;
        STATIC_FIELD = "clean";
        String a = STATIC_FIELD;
        sink(a);
    }

    public void staticFieldSource() {
        String a = SOURCE_FIELD;
        sink(a);
    }

    public void staticFieldSourceNegative() {
        String a = STATIC_FIELD;
        sink(a);
    }

    public void binaryFlow(int p) {
        int a = p + 1;
        sinkInt(a);
    }

    public void binaryFlowRight(int p) {
        int a = 2 * p;
        sinkInt(a);
    }

    public void binaryNegative(int p, int q) {
        int a = q + 1;
        sinkInt(a);
    }

    public void selfRead(String p) {
        Node n = new Node();
        Node m = new Node();
        m.val = p;
        n.next = m;
        n = n.next;
        sink(n.val);
    }

    public void selfReadNoResurrect(String p) {
        Node n = new Node();
        n.val = p;
        n.next = new Node();
        n = n.next;
        sink(n.val);
    }

    public void selfWrite(String p) {
        Node n = new Node();
        n.val = p;
        n.next = n;
        sink(n.next.val);
    }

    public void selfWriteNegative(String p) {
        Node n = new Node();
        Node m = new Node();
        m.val = p;
        n.next = m;
        n.next = n;
        sink(n.next.val);
    }

    public void branchFlow(String p, boolean c) {
        String a = "clean";
        if (c) {
            a = p;
        }
        sink(a);
    }

    public void loopFlow(String p, int n) {
        String a = "clean";
        String b = "clean";
        for (int i = 0; i < n; i++) {
            b = a;
            a = p;
        }
        sink(b);
    }

    public void loopNegative(String p, int n) {
        String a = "clean";
        String b = "clean";
        for (int i = 0; i < n; i++) {
            a = b;
            b = "clean";
        }
        sink(a);
    }

    public String exitFlow(String p) {
        String a = p;
        return a;
    }

    public String exitNegative(String p) {
        String a = "clean";
        return a;
    }

    public void sink(String data) {
    }

    public void sinkInt(int data) {
    }
}
