package sample.bidi;

/** Bytecode witnesses for boundary liveness. The analyzer does not execute these methods. */
public class BidiBoundaryLocalsSample {
    static void observe(Object value) { }
    static Object identity(Object value) { return value; }

    public static Object copies(Object input, boolean again) {
        Object x = identity(input);
        while (again) {
            Object tmp = x;
            observe(tmp);
        }
        return x;
    }

    public static Object carried(Object input, boolean again, boolean choose) {
        Object tmp = null;
        while (again) {
            if (choose) tmp = input;
            else observe(tmp);
        }
        return input;
    }
}
