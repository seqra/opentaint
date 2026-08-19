package test.samples;

public class BaseOnlyReferenceTransferFuzzSample {
    private static String source() { return "tainted"; }
    private static void sink(String value) { }
    private static String identity(String value) { return value; }

    private static PayloadBox makeBox(String value) { return new PayloadBox(value); }
    private static PayloadBox makeBoxDelegated(String value) { return makeBox(value); }
    private static Envelope makeEnvelope(PayloadBox box) { return new Envelope(box); }
    private static Envelope makeEnvelopeFromValue(String value) { return new Envelope(new PayloadBox(value)); }
    private static Outer makeOuter(String value) { return new Outer(new Envelope(new PayloadBox(value))); }
    private static void install(PayloadBox box, String value) { box.setPayload(value); }
    private static void installDelegated(PayloadBox box, String value) { install(box, value); }
    private static void installEnvelope(Envelope envelope, PayloadBox box) { envelope.setBox(box); }

    public static void directPayloadConstructor() { PayloadBox box = new PayloadBox(source()); sink(box.payload); }
    public static void identityPayloadConstructor() { PayloadBox box = new PayloadBox(identity(source())); sink(box.payload); }
    public static void payloadConstructorIntoLocal() { String value = source(); PayloadBox box = new PayloadBox(value); sink(box.payload); }
    public static void nestedEnvelopeConstructors() { Envelope envelope = new Envelope(new PayloadBox(source())); sink(envelope.box.payload); }
    public static void tripleNestedConstructors() { Outer outer = new Outer(new Envelope(new PayloadBox(source()))); sink(outer.envelope.box.payload); }
    public static void constructorAfterValueAlias() { String value = source(); String alias = value; PayloadBox box = new PayloadBox(alias); sink(box.payload); }
    public static void constructorAfterTwoValueAliases() { String value = source(); String first = value; String second = first; PayloadBox box = new PayloadBox(second); sink(box.payload); }
    public static void constructorThenWrapperAlias() { PayloadBox box = new PayloadBox(source()); PayloadBox alias = box; sink(alias.payload); }

    public static void directBoxFactory() { PayloadBox box = makeBox(source()); sink(box.payload); }
    public static void delegatedBoxFactory() { PayloadBox box = makeBoxDelegated(source()); sink(box.payload); }
    public static void envelopeFactory() { Envelope envelope = makeEnvelope(new PayloadBox(source())); sink(envelope.box.payload); }
    public static void envelopeFactoryFromValue() { Envelope envelope = makeEnvelopeFromValue(source()); sink(envelope.box.payload); }
    public static void outerFactoryFromValue() { Outer outer = makeOuter(source()); sink(outer.envelope.box.payload); }
    public static void factoryAfterValueAlias() { String value = source(); String alias = value; PayloadBox box = makeBox(alias); sink(box.payload); }

    public static void directPayloadSetter() { PayloadBox box = new PayloadBox(); box.setPayload(source()); sink(box.payload); }
    public static void setterAfterIdentity() { PayloadBox box = new PayloadBox(); box.setPayload(identity(source())); sink(box.payload); }
    public static void setterOnAliasedWrapper() { PayloadBox box = new PayloadBox(); PayloadBox alias = box; alias.setPayload(source()); sink(box.payload); }
    public static void helperPayloadSetter() { PayloadBox box = new PayloadBox(); install(box, source()); sink(box.payload); }
    public static void delegatedHelperPayloadSetter() { PayloadBox box = new PayloadBox(); installDelegated(box, source()); sink(box.payload); }
    public static void helperSetterOnAlias() { PayloadBox box = new PayloadBox(); PayloadBox alias = box; install(alias, source()); sink(box.payload); }
    public static void envelopeSetterAfterPayloadConstructor() { Envelope envelope = new Envelope(); installEnvelope(envelope, new PayloadBox(source())); sink(envelope.box.payload); }
    public static void envelopeSetterAfterPayloadSetter() { PayloadBox box = new PayloadBox(); box.setPayload(source()); Envelope envelope = new Envelope(); envelope.setBox(box); sink(envelope.box.payload); }

    public static void fluentPayloadSetter() { PayloadBox box = new PayloadBox().withPayload(source()); sink(box.payload); }
    public static void fluentPayloadAfterIdentity() { PayloadBox box = new PayloadBox().withPayload(identity(source())); sink(box.payload); }
    public static void fluentNestedEnvelope() { Envelope envelope = new Envelope().withBox(new PayloadBox().withPayload(source())); sink(envelope.box.payload); }

    public static void pairConstructorFirstPayload() { PayloadPair pair = new PayloadPair(source(), "clean"); sink(pair.first); }
    public static void pairConstructorSecondPayload() { PayloadPair pair = new PayloadPair("clean", source()); sink(pair.second); }
    public static void pairSetterFirstPayload() { PayloadPair pair = new PayloadPair(); pair.setBoth(source(), "clean"); sink(pair.first); }
    public static void pairSetterSecondPayload() { PayloadPair pair = new PayloadPair(); pair.setBoth("clean", source()); sink(pair.second); }
    public static void referenceArrayWrapper() { ArrayEnvelope envelope = new ArrayEnvelope(new String[]{source()}); sink(envelope.values[0]); }

    private static class PayloadBox {
        private String payload;
        PayloadBox() { }
        PayloadBox(String payload) { this.payload = payload; }
        void setPayload(String value) { payload = value; }
        PayloadBox withPayload(String value) { payload = value; return this; }
    }
    private static final class Envelope {
        private PayloadBox box;
        Envelope() { }
        Envelope(PayloadBox box) { this.box = box; }
        void setBox(PayloadBox box) { this.box = box; }
        Envelope withBox(PayloadBox box) { this.box = box; return this; }
    }
    private static final class Outer {
        private final Envelope envelope;
        Outer(Envelope envelope) { this.envelope = envelope; }
    }
    private static final class PayloadPair {
        private String first;
        private String second;
        PayloadPair() { }
        PayloadPair(String first, String second) { this.first = first; this.second = second; }
        void setBoth(String first, String second) { this.first = first; this.second = second; }
    }
    private static final class ArrayEnvelope {
        private final String[] values;
        ArrayEnvelope(String[] values) { this.values = values; }
    }
}
