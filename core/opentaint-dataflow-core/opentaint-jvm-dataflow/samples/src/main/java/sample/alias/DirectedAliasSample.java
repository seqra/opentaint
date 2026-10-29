package sample.alias;

public class DirectedAliasSample {

    static class Box {
        Object value;
        Box next;
    }

    static class Holder {
        Box box;
    }

    static class FinalBox {
        final Object value;

        FinalBox(Object value) {
            this.value = value;
        }
    }

    static Object staticField;

    static void joinOfAllocs(boolean c) {
        Object x = new Object();
        Object y = new Object();
        Object a;
        if (c) {
            a = x;
        } else {
            a = y;
        }
        probe(x, y, a);
    }

    static void joinOfArgs(Object px, Object py, boolean c) {
        Object x = px;
        Object y = py;
        Object a;
        if (c) {
            a = x;
        } else {
            a = y;
        }
        probe(x, y, a);
    }

    static void fieldWriteThroughJoinAllocs(boolean c) {
        Box x = new Box();
        Box y = new Box();
        Object z = new Object();
        Box a;
        if (c) {
            a = x;
        } else {
            a = y;
        }
        a.value = z;
        a = new Box();
        Object xv = x.value;
        Object yv = y.value;
        probe(z, x, y, xv, yv);
    }

    static void fieldWriteThroughJoinArgs(Box px, Box py, Object pz, boolean c) {
        Box x = px;
        Box y = py;
        Object z = pz;
        Box a;
        if (c) {
            a = x;
        } else {
            a = y;
        }
        a.value = z;
        a = new Box();
        Object xv = x.value;
        Object yv = y.value;
        probe(z, x, y, xv, yv);
    }

    static void storeThroughJoinLoadThroughOtherAllocs(boolean c) {
        Box x = new Box();
        Box y = new Box();
        Object z = new Object();
        Box a;
        if (c) {
            a = x;
        } else {
            a = y;
        }
        a.value = z;
        Object t = y.value;
        probe(t, z);
    }

    static void storeThroughJoinLoadThroughOtherArgs(Box px, Box py, Object pz, boolean c) {
        Box x = px;
        Box y = py;
        Object z = pz;
        Box a;
        if (c) {
            a = x;
        } else {
            a = y;
        }
        a.value = z;
        Object t = y.value;
        probe(t, z);
    }

    static void correlatedBranches(boolean c) {
        Object x = new Object();
        Object y = new Object();
        Object a;
        Object b;
        if (c) {
            a = x;
            b = y;
        } else {
            a = y;
            b = x;
        }
        probe(a, b);
    }

    static void loopReassign(int n) {
        Object a = new Object();
        Object b = new Object();
        Object cur = a;
        int i = 0;
        while (i < n) {
            cur = b;
            i++;
        }
        probe(a, b, cur);
    }

    static void heapChainAllocs() {
        Box x = new Box();
        Object y = new Object();
        x.value = y;
        Object z = x.value;
        probe(z, y, x);
    }

    static void loadThroughJoinOfArgs(Box p, Box q, boolean c) {
        Box a;
        if (c) {
            a = p;
        } else {
            a = q;
        }
        Object t = a.value;
        Object pv = p.value;
        probe(t, pv);
    }

    static void loopSiteStrongUpdateAfterInvalidatedLoad(Holder h, Object pa, Object pw, int n) {
        Box prev = h.box;
        touch(h);
        prev.value = pa;
        for (int i = 0; i < n; i++) {
            Object seen = prev.value;
            Box cur = new Box();
            cur.value = pw;
            probe(seen, prev, cur);
            cur.value = pa;
            prev = cur;
        }
    }

    static void loopSiteStrongUpdateAfterAllocatedPrev(Object pa, Object pw, int n) {
        Box prev = new Box();
        prev.value = pa;
        for (int i = 0; i < n; i++) {
            Object seen = prev.value;
            Box cur = new Box();
            cur.value = pw;
            probe(seen, prev, cur);
            cur.value = pa;
            prev = cur;
        }
    }

    static void loopSiteStrongUpdateAfterNullPrev(Object pa, Object pw, int n) {
        Box prev = null;
        for (int i = 0; i < n; i++) {
            Box cur = new Box();
            if (prev != null) {
                Object seen = prev.value;
                cur.value = pw;
                probe(seen, prev, cur);
            }
            cur.value = pa;
            prev = cur;
        }
    }

    static void loopSiteStrongUpdateAfterArgPrev(Box p, Object pa, Object pw, int n) {
        Box prev = p;
        prev.value = pa;
        for (int i = 0; i < n; i++) {
            Object seen = prev.value;
            Box cur = new Box();
            cur.value = pw;
            probe(seen, prev, cur);
            cur.value = pa;
            prev = cur;
        }
    }

    static void joinOfInvalidatedLoadAndAlloc(Holder h, Object pa, Object pw, boolean c) {
        Box p = h.box;
        touch(h);
        p.value = pa;
        Object seen = p.value;
        Box n;
        if (c) {
            n = p;
        } else {
            n = new Box();
        }
        n.value = pw;
        probe(seen, n, p);
    }

    static void loopSiteStrongUpdateAfterCallReturnPrev(Object pa, Object pw, int n) {
        Box prev = makeBox();
        prev.value = pa;
        for (int i = 0; i < n; i++) {
            Object seen = prev.value;
            Box cur = new Box();
            cur.value = pw;
            probe(seen, prev, cur);
            cur.value = pa;
            prev = cur;
        }
    }

    static class CtorLoop extends Box {
        CtorLoop(Object pa, Object pw, int n) {
            this.value = pa;
            Box prev = this;
            for (int i = 0; i < n; i++) {
                Object seen = prev.value;
                Box cur = new Box();
                cur.value = pw;
                probe(seen, prev, cur);
                cur.value = pa;
                prev = cur;
            }
        }
    }

    static class CtorJoin extends Box {
        CtorJoin(Object pa, Object pw, boolean c) {
            this.value = pa;
            Object seen = this.value;
            Box n;
            if (c) {
                n = this;
            } else {
                n = new Box();
            }
            n.value = pw;
            probe(seen, n);
        }
    }

    static void loadThenUnknownCallArg(Box x) {
        Object w = x.value;
        touch(x);
        probe(w);
    }

    static void loadThenUnknownCallLocal(Object v) {
        Box x = new Box();
        x.value = v;
        Object w = x.value;
        touch(x);
        probe(w, x);
    }

    static void loadThenUnrelatedCallArg(Box x, Object other) {
        Object w = x.value;
        touch(other);
        probe(w);
    }

    static void loadThenUnrelatedCallCopiedArg(Box px, Object other) {
        Box x = px;
        Object w = x.value;
        touch(other);
        probe(w, x);
    }

    static void loadThenUnknownCallFinalArg(FinalBox x) {
        Object w = x.value;
        touch(x);
        probe(w);
    }

    static void loadThenUnknownCallFinalLocal(Object v) {
        FinalBox x = new FinalBox(v);
        Object w = x.value;
        touch(x);
        probe(w, x);
    }

    static void loadThenJdkCallArg(Box x, StringBuilder sb) {
        Object w = x.value;
        sb.append(x);
        probe(w);
    }

    static void staticWriteThenRead() {
        Object v = new Object();
        staticField = v;
        Object t = staticField;
        probe(t, v);
    }

    static class ThisWrites extends Box {
        ThisWrites(Object p1, Object p2) {
            Object v1 = p1;
            Object v2 = p2;
            this.value = v1;
            this.value = v2;
            Object t = this.value;
            probe(t, v1, v2);
        }

        void method(Object p1, Object p2) {
            Object v1 = p1;
            Object v2 = p2;
            this.value = v1;
            this.value = v2;
            Object t = this.value;
            probe(t, v1, v2);
        }
    }

    static void passThroughOfTwoArgs(Object px, Object py) {
        Object x = px;
        Object y = py;
        Object r = choose(x, y);
        probe(x, y, r);
    }

    static Object choose(Object a, Object b) {
        return a;
    }

    static void selfCopyAlloc() {
        Object x = new Object();
        Object z = x;
        x = x;
        probe(x, z);
    }

    static void selfCopyArg(Object p) {
        Object x = p;
        Object z = x;
        x = x;
        probe(x, z);
    }

    static void selfCast() {
        Object x = new Box();
        Object z = x;
        x = (Box) x;
        probe(x, z);
    }

    static void reprLoadArg(Box p) {
        Box x = p;
        Box w = p.next;
        x = x.next;
        probe(x, w);
    }

    static void reprLoadOther(Box p) {
        Box x = p;
        Box w = p.next;
        x = p.next;
        probe(x, w);
    }

    static void reprLoadIntoLiveRoot(Box p) {
        Box x = p;
        Box w = x.next;
        x = p.next;
        probe(x, w);
    }

    static void reprLoadIntoLiveRootHeap(Holder h) {
        Box x = null;
        Box y = h.box;
        x = y;
        Box w = x.next;
        x = y.next;
        probe(x, w, y);
    }

    static void reprLoadIntoLiveRootLoop(Box head, int n) {
        Box cur = head;
        Box second = cur.next;
        for (int i = 0; i < n; i++) {
            cur = head.next;
        }
        probe(cur, second);
    }

    static void reprLoadRightAfterCopy(Box p) {
        Box w = p.next;
        Box x = p;
        x = p.next;
        probe(x, w);
    }

    static void reprLoadRightAfterCopyAlone(Box p) {
        Box x = p;
        x = p.next;
        probe(x);
    }

    static void reprLoadConditional(Box p, boolean c) {
        Box w = p.next;
        Box x = p;
        if (c) {
            x = p.next;
        }
        probe(x, w);
    }

    static void reprLoadInLoop(Box head, int n) {
        Box second = head.next;
        Box cur = head;
        for (int i = 0; i < n; i++) {
            if (i == 1) {
                cur = head.next;
            }
        }
        probe(cur, second);
    }

    static void reprLoadOtherHeap(Holder h) {
        Box y = h.box;
        Box x = y;
        Box w = y.next;
        x = y.next;
        probe(x, w, y);
    }

    static void reprLoadOtherAlloc() {
        Box y = new Box();
        y.next = new Box();
        Box x = y;
        Box w = y.next;
        x = y.next;
        probe(x, w, y);
    }

    static void reprLoadAlloc() {
        Box p = new Box();
        p.next = new Box();
        Box x = p;
        Box w = p.next;
        x = x.next;
        probe(x, w);
    }

    static void reprLoadCast(Box p) {
        Object x = p;
        Object w = p.value;
        x = ((Box) x).value;
        probe(x, w);
    }

    static void listWalk(Box head) {
        Box cur = head;
        while (cur.next != null) {
            cur = cur.next;
        }
        probe(cur);
    }

    static void listWalkWithSecond(Box head) {
        Box second = head.next;
        Box cur = head;
        while (cur.next != null) {
            cur = cur.next;
        }
        probe(cur, second);
    }

    static void listStepsWithSecond(Box head, int n) {
        Box cur = head;
        Box second = head.next;
        for (int i = 0; i < n; i++) {
            cur = cur.next;
        }
        probe(cur, second);
    }

    static Box makeBox() {
        return new Box();
    }

    static void touch(Object o) {
    }

    static void probe(Object a) {
    }

    static void probe(Object a, Object b) {
    }

    static void probe(Object a, Object b, Object c) {
    }

    static void probe(Object a, Object b, Object c, Object d) {
    }

    static void probe(Object a, Object b, Object c, Object d, Object e) {
    }
}
