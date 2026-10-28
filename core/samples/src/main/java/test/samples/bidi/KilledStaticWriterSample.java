package test.samples.bidi;

/** Exit rules remove output after the body has read it into the return value. */
public class KilledStaticWriterSample {
    public static Object output;

    public static Object source() { return new Object(); }
    public static void sink(Object value) { }

    public static Object writeRead() {
        output = source();
        return output;
    }

    public static Object writeReadUnmarked() {
        output = new Object();
        return output;
    }

    public static Object wrap() { return writeRead(); }
    public static Object wrapDeep() { return wrap(); }

    public static void direct() { sink(writeRead()); }
    public static void nested() { sink(wrapDeep()); }
    public static void noSource() { sink(writeReadUnmarked()); }
}
