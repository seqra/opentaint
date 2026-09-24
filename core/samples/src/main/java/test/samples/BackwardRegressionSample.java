package test.samples;

public class BackwardRegressionSample {
    public static class SbHolder {
        public StringBuilder sb = new StringBuilder();
    }

    public static StringBuilder staticSb = new StringBuilder();

    public static String STATIC_SOURCE = "static";

    public StringBuilder sbField = new StringBuilder();

    public void throwingBranch(String p, boolean c) {
        if (c) {
            sink(p);
            throw new IllegalArgumentException("bad");
        }
    }

    public void infiniteLoop(String p) {
        while (true) {
            sink(p);
        }
    }

    public void failWith(String p) {
        sink(p);
        throw new IllegalStateException();
    }

    public void callsFailing(String p) {
        failWith(p);
    }

    public void catchThenRethrow(String p) {
        try {
            mayFail();
        } catch (IllegalStateException e) {
            sink(p);
            throw new RuntimeException(e);
        }
    }

    public void taintThenThrow(SbHolder h, String p) {
        h.sb.append(p);
        throw new IllegalStateException();
    }

    public void callsTaintThenThrow(String p) {
        SbHolder h = new SbHolder();
        try {
            taintThenThrow(h, p);
        } catch (IllegalStateException e) {
        }
        sink(h.sb.toString());
    }

    public void aliasOnArgumentPath(String p, SbHolder h) {
        StringBuilder b = h.sb;
        b.append(p);
        sink(h.sb.toString());
    }

    public void aliasOnThisPath(String p) {
        StringBuilder b = this.sbField;
        b.append(p);
        sink(this.sbField.toString());
    }

    public void aliasOnLocalPath(String p) {
        SbHolder h = new SbHolder();
        StringBuilder b = h.sb;
        b.append(p);
        sink(h.sb.toString());
    }

    public void aliasOnStaticPath(String p) {
        StringBuilder b = staticSb;
        b.append(p);
        sink(staticSb.toString());
    }

    public void entryHandler(String p) {
    }

    public void callsEntryHandler(String s) {
        entryHandler(s);
        sink(s);
    }

    public void entryHandlerStores(String p, SbHolder h) {
        h.sb.append(p);
    }

    public void callsEntryHandlerStoring(String s) {
        SbHolder h = new SbHolder();
        entryHandlerStores(s, h);
        sink(h.sb.toString());
    }

    public String entryHandlerReturns(String p) {
        return p;
    }

    public void callsEntryHandlerReturning(String s) {
        String r = entryHandlerReturns(s);
        sink(r);
    }

    public void entryHandlerSinks(String p) {
        sink(p);
    }

    public void callsEntryHandlerSinking(String s) {
        entryHandlerSinks(s);
    }

    public void entryHandlerPublishes(String p) {
        staticSb.append(p);
    }

    public void callsEntryHandlerPublishing(String s) {
        entryHandlerPublishes(s);
        sink(staticSb.toString());
    }

    public void callSourceFlow() {
        String s = source();
        sink(s);
    }

    public void entrySourceFlow(String p) {
        sink(p);
    }

    public void exitSourceFlow() {
        String s = exitSource();
        sink(s);
    }

    public void staticSourceFlow() {
        String s = STATIC_SOURCE;
        sink(s);
    }

    public String exitSource() {
        return "exit";
    }

    public String source() {
        return "tainted";
    }

    public void mayFail() {
    }

    public void sink(String data) {
    }
}
