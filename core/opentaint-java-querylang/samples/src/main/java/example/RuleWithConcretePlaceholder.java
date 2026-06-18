package example;

import base.RuleSample;
import base.RuleSet;

@RuleSet("example/RuleWithConcretePlaceholder.yaml")
public abstract class RuleWithConcretePlaceholder implements RuleSample {
    public static String source() {
        return "tainted";
    }

    static class Engine {
        public void foo(String a, String b, Context data, String d) {

        }
    }

    static class Context {
        void put(String a, String data) {
        }
    }

    static class PositiveFoo extends RuleWithConcretePlaceholder {
        @Override
        public void entrypoint() {
            Context context = new Context();
            Engine engine = new Engine();

            String data = source();
            context.put("data", data);
            engine.foo("a", "b", context, "d");
        }
    }

}
