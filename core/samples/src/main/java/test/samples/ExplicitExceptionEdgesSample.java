package test.samples;

public class ExplicitExceptionEdgesSample {
    public static void caughtExplicitThrow(boolean fail) {
        try {
            implicitThrower();
            if (fail) {
                throw new IllegalArgumentException("explicit");
            }
            Runnable callback = () -> consume(new RuntimeException("lambda"));
            callback.run();
            lastTryStatement();
        } catch (RuntimeException exception) {
            consume(exception);
        }
    }

    private static void implicitThrower() {
        throw new IllegalStateException("callee");
    }

    private static void lastTryStatement() {
        // Keep a non-throw statement at the end of the protected region.
    }

    private static void consume(RuntimeException exception) {
        // Keep the catch handler in bytecode.
    }
}
