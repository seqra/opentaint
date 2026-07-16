package test.samples;

public class BaseOnlyTraceResolutionFuzzSample {
    private static String source() { return "tainted"; }
    private static void sink(String value) { }

    private static Box box(String value) { return new Box(value); }
    private static Envelope envelope(String value) { return new Envelope(new Box(value)); }
    private static Envelope envelopeViaBox(String value) { return new Envelope(box(value)); }
    private static Envelope delegatedEnvelope(String value) { return envelope(value); }
    private static Outer outer(String value) { return new Outer(new Envelope(new Box(value))); }
    private static Outer outerViaEnvelope(String value) { return new Outer(envelope(value)); }
    private static Outer delegatedOuter(String value) { return outer(value); }

    public static void nestedFactory() {
        Envelope result = envelope(source());
        sink(result.box.value);
    }

    public static void nestedFactoryViaBoxFactory() {
        Envelope result = envelopeViaBox(source());
        sink(result.box.value);
    }

    public static void delegatedNestedFactory() {
        Envelope result = delegatedEnvelope(source());
        sink(result.box.value);
    }

    public static void threeLevelFactory() {
        Outer result = outer(source());
        sink(result.envelope.box.value);
    }

    public static void threeLevelFactoryViaEnvelopeFactory() {
        Outer result = outerViaEnvelope(source());
        sink(result.envelope.box.value);
    }

    public static void delegatedThreeLevelFactory() {
        Outer result = delegatedOuter(source());
        sink(result.envelope.box.value);
    }

    private static final class Box {
        private final String value;

        private Box(String value) { this.value = value; }
    }

    private static final class Envelope {
        private final Box box;

        private Envelope(Box box) { this.box = box; }
    }

    private static final class Outer {
        private final Envelope envelope;

        private Outer(Envelope envelope) { this.envelope = envelope; }
    }
}
