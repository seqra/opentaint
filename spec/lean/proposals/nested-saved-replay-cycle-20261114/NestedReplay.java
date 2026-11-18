/** Synthetic reachability sample. Rules are defined in the companion report. */
final class NestedReplay {
    static final class Node {
        Node f;
        Node g;
        Node() {}
    }

    static Node produce() {
        Node x = new Node();
        x.f = new Node();
        x.f.g = new Node();
        return x;
    }

    static void observe(Node x) {}

    static Node choose(Node x, boolean down) {
        if (down) return x.f.f;
        Node t = new Node();
        t.f = x;
        Node y = new Node();
        y.f = t;
        return y;
    }

    static Node wrapper(Node x, boolean down) {
        return choose(x, down);
    }

    static void entry(boolean b1, boolean b2, boolean b3) {
        Node x = produce();
        Node y = wrapper(x, b1);
        Node z = wrapper(y, b2);
        Node w = wrapper(z, b3);
        observe(w);
    }
}
