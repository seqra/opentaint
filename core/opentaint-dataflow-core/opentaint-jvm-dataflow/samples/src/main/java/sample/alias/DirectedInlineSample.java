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

    static Box makeFirst() {
        return new Box();
    }

    static Box makeSecond() {
        return new Box();
    }

    static Box fail() {
        throw new IllegalStateException();
    }

    // Two consecutive call statements. A test resolves each call to many overrides.
    static void twoCallsWithManyOverrides(Object x, Object y) {
        Box a = makeFirst();
        Box b = makeSecond();
        a.value = x;
        b.value = y;
        Object t = a.value;
        probe(t, a, b);
    }

    static class Toucher {
        void touch(Box x) {
        }
    }

    static class NativeToucher extends Toucher {
        @Override
        native void touch(Box x);
    }

    static class PlainToucher {
        void touch(Box x) {
        }
    }

    // The call has an override with a body and an override without a body (a native method). The
    // native override can write `x.next`, so the store `t.value = v` is weak: `w` also keeps the old value.
    static void bodilessOverride(Toucher m, Box x, Object v) {
        Box e = x.next;
        m.touch(x);
        Box t = x.next;
        t.value = v;
        Object w = e.value;
        probe(w, v, x);
    }

    // The same program with one override that has a body: the store `t.value = v` is strong.
    static void bodyOnlyOverride(PlainToucher m, Box x, Object v) {
        Box e = x.next;
        m.touch(x);
        Box t = x.next;
        t.value = v;
        Object w = e.value;
        probe(w, v, x);
    }

    static void probe(Object a, Object b, Object c) {
    }
}
