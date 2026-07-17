package test.samples;

public class BaseOnlyTraceProjectionFuzzSample {
    private static Outer source() { return null; }
    private static void sink(Token value) { }

    private static Envelope projectEnvelope(Outer value) {
        return value.envelope;
    }

    public static void projectOneLevel() {
        Outer value = source();
        Envelope result = projectEnvelope(value);
        sink(result.box.value);
    }

    private static Token projectToken(Outer value) {
        return projectEnvelope(value).box.value;
    }

    public static void projectThreeLevels() {
        Outer value = source();
        sink(projectToken(value));
    }

    private static Outer relayOuter(Outer value) { return value; }
    private static Envelope relayEnvelope(Envelope value) { return value; }

    public static void relayThenProject() {
        Outer value = relayOuter(source());
        Envelope result = relayEnvelope(projectEnvelope(value));
        sink(result.box.value);
    }

    private static void touchOuter(Outer value) { value.other = new Token(); }
    private static void touchEnvelope(Envelope value) { value.other = new Token(); }
    private static void touchBox(Box value) { value.other = new Token(); }

    public static void mutateThenProject() {
        Outer value = source();
        touchOuter(value);
        touchEnvelope(value.envelope);
        touchBox(value.envelope.box);
        sink(projectToken(value));
    }

    private static final class Token { }

    private static final class Box {
        Token value;
        Token other;
    }

    private static final class Envelope {
        Box box;
        Token other;
    }

    private static final class Outer {
        Envelope envelope;
        Token other;
    }
}
