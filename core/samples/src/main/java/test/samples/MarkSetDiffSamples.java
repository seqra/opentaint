package test.samples;

/**
 * Mark-set differential samples (spec §8 Layer 3): each program runs under the baseline and
 * under the mark-set selection, and the two finding sets must be equal.
 */
public class MarkSetDiffSamples {

    /* ---------- D1: two entry points, a conjunctive sink in a shared callee ---------- */

    public void d1EntryOne() {
        d1Shared(sourceA(), "safe");
    }

    public void d1EntryTwo() {
        d1Shared("safe", sourceB());
    }

    private void d1Shared(String first, String second) {
        sinkBoth(first, second);
    }

    /* ---------- G1: a sink's end fact used across roots ---------- */

    public void g1EntryOne() {
        String data = sourceA();
        g1Shared(data);
        sinkChecked(data);
    }

    public void g1EntryTwo() {
        String data = "safe";
        g1Shared(data);
        sinkChecked(data);
    }

    public void g1EntryCleaned() {
        String data = sourceA();
        check(data);
        uncheck(data);
    }

    private void g1Shared(String data) {
        check(data);
    }

    /* ---------- G4: a mark-conditioned cleaner on a field tree holding a needed mark ---------- */

    public static class Pair {
        public String first;
    }

    public void g4EntryFieldCleaned() {
        Pair pair = new Pair();
        pair.first = sourceA();
        addBPair(pair);
        cleanIfB(pair);
        sink(pair.first);
    }

    public void g4EntryKept() {
        Pair pair = new Pair();
        pair.first = sourceA();
        cleanIfB(pair);
        sink(pair.first);
    }

    /* ---------- G5: an exit sink on a fact-to-fact edge, and one on a zero-to-fact edge ---------- */

    public void g5Entry() {
        String passed = g5PassBack(sourceA());
        String produced = g5Produce();
        consume(passed, produced);
    }

    public String g5PassBack(String data) {
        return data;
    }

    public String g5Produce() {
        return sourceA();
    }

    /* ---------- G6: an exit source at a throw, observed by an exit sink there ---------- */

    public void g6Entry() {
        g6Throw();
    }

    public String g6Throw() {
        RuntimeException ex = sourceException();
        throw ex;
    }

    /* ---------- D4: a chain source -> transformer -> sink, plus an unrelated rule ---------- */

    public void d4Entry() {
        String data = sourceA();
        String transformed = transform(data);
        sinkTransformed(transformed);

        String unrelated = sourceUnrelated();
        consume(unrelated, unrelated);
    }

    /* ---------- rule targets ---------- */

    public String sourceA() { return "a"; }
    public String sourceB() { return "b"; }
    public String sourceUnrelated() { return "u"; }
    public RuntimeException sourceException() { return new RuntimeException(); }

    public String transform(String data) { return data; }

    public void sink(String data) { }
    public void sinkBoth(String first, String second) { }
    public void sinkChecked(String data) { }
    public void sinkTransformed(String data) { }
    public void sinkUnrelated(String data) { }

    public void check(String data) { }
    public void uncheck(String data) { }
    public void cleanIfB(Pair pair) { }
    public void addBPair(Pair pair) { }
    public void consume(String first, String second) { }
}
