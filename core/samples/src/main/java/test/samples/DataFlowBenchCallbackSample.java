package test.samples;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.IntConsumer;

public class DataFlowBenchCallbackSample {

    static final class IntRegistry {
        private final List<IntConsumer> hooks = new ArrayList<>();

        void register(IntConsumer hook) {
            hooks.add(hook);
        }

        void fire(int value) {
            for (IntConsumer hook : hooks) {
                hook.accept(value);
            }
        }
    }

    static final class StringRegistry {
        private final List<Consumer<String>> hooks = new ArrayList<>();

        void register(Consumer<String> hook) {
            hooks.add(hook);
        }

        void fire(String value) {
            for (Consumer<String> hook : hooks) {
                hook.accept(value);
            }
        }
    }

    public void callbackIntFlow() {
        IntRegistry registry = new IntRegistry();
        registry.register(value -> intSink(value));
        registry.fire(intSource());
    }

    public void callbackStringFlow() {
        StringRegistry registry = new StringRegistry();
        registry.register(value -> sink(value));
        registry.fire(source());
    }

    public void directLambdaFlow() {
        Consumer<String> hook = value -> sink(value);
        hook.accept(source());
    }

    public void listIterationFlow() {
        List<String> items = new ArrayList<>();
        items.add(source());
        for (String item : items) {
            sink(item);
        }
    }

    public int intSource() { return 1; }

    public void intSink(int data) { }

    public String source() { return "tainted"; }

    public void sink(String data) { }
}
