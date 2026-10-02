package test.samples;

/**
 * Mark-set prescan recording sample: a virtual call, a lambda call, a static-field read,
 * a throwing method with an exit sink, a cleaner call, and two entry points sharing a callee.
 */
public class MarkSetSample {
    private static String staticField;

    public interface Handler {
        void handle(String data);
    }

    public static class HandlerImpl implements Handler {
        @Override
        public void handle(String data) {
            new MarkSetSample().sink(data);
        }
    }

    public void entryOne() throws Exception {
        String data = source();
        Handler handler = new HandlerImpl();
        handler.handle(data);

        Runnable action = () -> sink(data);
        action.run();

        String fromField = staticField;
        String cleaned = clean(fromField);
        shared(cleaned);

        throwing(data);
    }

    public void entryTwo() {
        shared(source());
    }

    private void shared(String data) {
        sink(data);
    }

    public String throwing(String data) throws Exception {
        if (data.isEmpty()) {
            throw new Exception(data);
        }
        return data;
    }

    public String clean(String data) { return data; }

    public String source() { return "tainted"; }
    public void sink(String data) { }
}
