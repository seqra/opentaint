package test.samples;

public class AnyFieldPrimitiveSample {
    public void sink(byte data) { }

    // The taint enters on a primitive array. An element read puts the any-field part
    // of the taint on a primitive position.
    public void elementFlow(byte[] digest) {
        for (byte b : digest) {
            sink(b);
        }
    }
}
