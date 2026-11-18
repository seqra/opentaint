/** Readable ordinary-code notation for the synthetic core-form witness.
 * The analysis fixture uses an atomic nested write(base,[f,g],strong).
 * This file is not a claim about Java-front-end lowering. */
final class NestedWriteCycle {
    static final class Node { Node f; Node g; }

    static Node produce() {
        Node x = new Node();
        x.f = new Node();
        x.f.f = new Node();
        x.g = new Node();
        return x;
    }

    static Node choose(Node x, boolean down) {
        x.f.g = new Node();
        Node y;
        if (down) {
            y = x.f;
        } else {
            y = new Node();
            y.f = x;
        }
        y.f.g = new Node();
        return y;
    }

    static void observe(Node y) { }

    static void entry(boolean down) {
        Node x = produce();  // Call-site rule assigns T at x.g and descendants.
        Node y = choose(x, down);
        observe(y);          // Call-site rule checks CM(y.[any],T).
    }
}
