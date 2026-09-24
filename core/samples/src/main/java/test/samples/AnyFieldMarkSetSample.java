package test.samples;

public class AnyFieldMarkSetSample {
    public static class Box {
        public String a;
        public String b;
    }

    public String sourceA() {
        return "a";
    }

    public String sourceB() {
        return "b";
    }

    public void sink(Box box) { }

    private void consume(Box box) {
        sink(box);
    }

    private void fillA(Box box, String a) {
        box.a = a;
        consume(box);
    }

    public void twoMarksTwoFrames() {
        Box box = new Box();
        box.b = sourceB();
        fillA(box, sourceA());
    }
}
