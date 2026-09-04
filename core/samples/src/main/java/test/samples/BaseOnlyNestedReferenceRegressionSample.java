package test.samples;

public class BaseOnlyNestedReferenceRegressionSample {
    private static String source() { return "tainted"; }
    private static void sink(String value) { }

    public static void nestedReferenceFlow() {
        Payload payload = new Payload(source());
        Envelope envelope = new Envelope(payload);
        sink(envelope.payload.value);
    }

    private static final class Payload {
        private final String value;

        private Payload(String value) {
            this.value = value;
        }
    }

    private static final class Envelope {
        private final Payload payload;

        private Envelope(Payload payload) {
            this.payload = payload;
        }
    }
}
