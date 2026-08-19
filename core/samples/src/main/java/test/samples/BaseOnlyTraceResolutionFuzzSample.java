package test.samples;

public class BaseOnlyTraceResolutionFuzzSample {
    private static String source() { return "tainted"; }
    private static void sink(String value) { }

    private static Envelope envelope(String value) { return new Envelope(new Box(value)); }

    public static void nestedFactory() {
        Envelope result = envelope(source());
        sink(result.box.value);
    }

    private static final class Box {
        String value;

        private Box(String value) { this.value = value; }
    }

    private static final class Envelope {
        final Box box;

        private Envelope(Box box) { this.box = box; }
    }
}
