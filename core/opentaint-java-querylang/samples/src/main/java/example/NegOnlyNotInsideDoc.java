package example;

import base.RuleSample;
import base.RuleSet;

/**
 * Doc validation: documents that a pattern-not-inside whose metavariables
 * exist only in the negative clause is silently ineffective.
 */
@RuleSet("example/NegOnlyNotInsideDoc.yaml")
public abstract class NegOnlyNotInsideDoc implements RuleSample {

    static class Client {
        static Client builder() { return new Client(); }
        void configure(String mode) {}
        void connect(String url) {}
    }

    static class Positive extends NegOnlyNotInsideDoc {
        @Override
        public void entrypoint() {
            Client c = Client.builder();
            c.connect("http://example.com");
        }
    }

    static class PositiveNotYetExcluded extends NegOnlyNotInsideDoc {
        @Override
        public void entrypoint() {
            Client f = Client.builder();
            f.configure("mode");
            Client c = Client.builder();
            c.connect("http://example.com");
        }
    }
}
