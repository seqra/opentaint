package test.samples;

public class SuffixTreePropagationSample {
    static class Pair {
        String left;
        String right;
    }

    public void commonBaseIdentityEntry(Pair pair) {
        preserveBoth(pair);
        sink(pair.left);
        sink(pair.right);
    }

    private void preserveBoth(Pair pair) {
        String left = pair.left;
        String right = pair.right;
        consume(left, right);
    }

    private void consume(String left, String right) { }

    public void sink(String value) { }
}
