package test;

public final class Taint {

    private Taint() {
    }

    public static <T> T source() {
        return null;
    }

    public static void sink(Object value) {
    }
}
