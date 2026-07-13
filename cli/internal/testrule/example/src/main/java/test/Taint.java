package test;

/**
 * Generic taint marker for rule test projects. {@code source()} is generic so it
 * assigns to any type without a cast (it erases to {@code Object}); {@code sink(Object)}
 * accepts any value. Matched by the bundled generic-source / generic-sink lib rules, so a
 * package's source/sink lib rules can be exercised against a fixed, type-agnostic counterpart.
 */
public final class Taint {

    private Taint() {
    }

    @SuppressWarnings("unchecked")
    public static <T> T source() {
        return (T) new Object();
    }

    public static void sink(Object value) {
    }
}
