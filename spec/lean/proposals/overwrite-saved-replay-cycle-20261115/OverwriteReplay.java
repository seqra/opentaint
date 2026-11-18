// Fully analyzed synthetic data-flow example. No intrinsic transfer model.
final class Node { Node f; Node g; Node() {} }

final class OverwriteReplay {
    // Marking rule on this call: assign full mark T at return.f.g and below.
    static Node produce() {
        Node x = new Node();
        x.f = new Node(); x.f.g = new Node();
        x.f.f = new Node(); x.f.f.f = new Node();
        x.f.f.f.f = new Node(); x.f.f.f.f.f = new Node();
        x.f.f.f.f.f.f = new Node();
        return x;
    }
    // Observation rule on this call: CM(argument-0.[any], T).
    static void observe(Node x) {}
    static Node choose(Node x, boolean down) {
        x.g = new Node();
        Node y;
        if (down) {
            y = x.f.f;
        } else {
            Node t = new Node(); t.f = x;
            y = new Node(); y.f = t;
        }
        y.g = new Node();
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
