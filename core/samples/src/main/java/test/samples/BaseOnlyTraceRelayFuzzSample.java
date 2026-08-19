package test.samples;

public class BaseOnlyTraceRelayFuzzSample {
    private static Token source() { return new Token(); }
    private static void sink(Token value) { }

    private static Envelope identity(Envelope value) { return value; }

    private static Envelope identityFactory(Token value) {
        Envelope envelope = new Envelope(new Box(value));
        return identity(envelope);
    }

    public static void returnThroughIdentity() {
        Envelope result = identityFactory(source());
        sink(result.box.value);
    }

    private static Envelope doubleIdentityFactory(Token value) {
        Envelope envelope = new Envelope(new Box(value));
        return identity(identity(envelope));
    }

    public static void returnThroughDoubleIdentity() {
        Envelope result = doubleIdentityFactory(source());
        sink(result.box.value);
    }

    private static Envelope instanceIdentityFactory(Token value) {
        Envelope envelope = new Envelope(new Box(value));
        return envelope.self();
    }

    public static void returnThroughInstanceIdentity() {
        Envelope result = instanceIdentityFactory(source());
        sink(result.box.value);
    }

    private static Envelope interfaceIdentityFactory(Token value) {
        Envelope envelope = new Envelope(new Box(value));
        EnvelopeRelay relay = new EnvelopeRelayImpl();
        return relay.relay(envelope);
    }

    public static void returnThroughInterfaceIdentity() {
        Envelope result = interfaceIdentityFactory(source());
        sink(result.box.value);
    }

    private static Envelope branchIdentityFactory(Token value) {
        Envelope envelope = new Envelope(new Box(value));
        return choose(envelope, new Envelope(new Box()));
    }

    private static Envelope choose(Envelope first, Envelope second) {
        return first != null ? first : second;
    }

    public static void returnThroughBranchIdentity() {
        Envelope result = branchIdentityFactory(source());
        sink(result.box.value);
    }

    private static Outer outerIdentity(Outer value) { return value; }

    private static Outer outerIdentityFactory(Token value) {
        Outer outer = new Outer(new Envelope(new Box(value)));
        return outerIdentity(outer);
    }

    public static void returnOuterThroughIdentity() {
        Outer result = outerIdentityFactory(source());
        sink(result.envelope.box.value);
    }

    private static final class Token { }

    private static final class Box {
        Token value;

        Box() { }
        Box(Token value) { this.value = value; }
    }

    private static final class Envelope {
        Box box;

        Envelope(Box box) { this.box = box; }
        Envelope self() { return this; }
    }

    private static final class Outer {
        Envelope envelope;

        Outer(Envelope envelope) { this.envelope = envelope; }
    }

    private interface EnvelopeRelay {
        Envelope relay(Envelope value);
    }

    private static final class EnvelopeRelayImpl implements EnvelopeRelay {
        @Override
        public Envelope relay(Envelope value) { return value; }
    }
}
