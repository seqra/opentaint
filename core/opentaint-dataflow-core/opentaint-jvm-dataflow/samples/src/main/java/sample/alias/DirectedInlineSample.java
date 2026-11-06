package sample.alias;

/**
 * Samples of the inlining of resolved calls in the directed alias analysis (IMPL §5.5).
 */
public class DirectedInlineSample {

    static class Box {
        Object value;
        Box next;
    }

    static class Thrower {
        Object f;

        void setAndThrow(Object a) {
            this.f = a;
            throw new IllegalStateException();
        }
    }

    // Lean `inlined_answer`: the callee writes `this.f = a` and throws. The caller handler reads `x.f`.
    static void handlerSeesCalleeWrite(Object pa) {
        Thrower x = new Thrower();
        Object a = pa;
        try {
            x.setAndThrow(a);
        } catch (IllegalStateException e) {
            Object t = x.f;
            probe(t, a, x);
        }
    }

    static Box make() {
        return new Box();
    }

    static void twoMakes() {
        Box a = make();
        Box b = make();
        probe(a, b, null);
    }

    static Object nullValue() {
        return null;
    }

    static void nullTwice() {
        Object a = nullValue();
        Object b = nullValue();
        probe(a, b, null);
    }

    static void makeInLoop(int n) {
        Box last = null;
        for (int i = 0; i < n; i++) {
            Box b = make();
            b.next = last;
            last = b;
        }
        probe(last, null, null);
    }

    static void passOn(Box b) {
        probe(b, null, null);
    }

    static void unresolvedCallInCallee(Box x) {
        Object t = x.value;
        passOn(x);
        probe(t, x, null);
    }

    static Object pick(Object a, Object b, boolean c) {
        if (c) {
            return a;
        }
        return b;
    }

    static void returnsOfOneCallee(Object pa, Object pb, boolean c) {
        Object r = pick(pa, pb, c);
        probe(r, null, null);
    }

    static Object constantArgument() {
        Object r = identity("s");
        return r;
    }

    static Object identity(Object o) {
        return o;
    }

    static void probe(Object a, Object b, Object c) {
    }
}
