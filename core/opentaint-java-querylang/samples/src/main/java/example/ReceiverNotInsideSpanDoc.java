package example;

import base.RuleSample;
import base.RuleSet;

/**
 * Doc validation: receiver-position pattern-not-inside against a multi-event
 * main pattern — does the excluded context need to contain the whole span or
 * only the accepting event?
 */
@RuleSet("example/ReceiverNotInsideSpanDoc.yaml")
public abstract class ReceiverNotInsideSpanDoc implements RuleSample {

    static class Client {
        static Client builder() { return new Client(); }
        void allowHost(String host) {}
        void connect(String url) {}
    }

    static class Positive extends ReceiverNotInsideSpanDoc {
        @Override
        public void entrypoint() {
            Client c = Client.builder();
            c.connect("http://example.com");
        }
    }

    static class Negative extends ReceiverNotInsideSpanDoc {
        @Override
        public void entrypoint() {
            Client c = Client.builder();
            c.allowHost("trusted.example");
            c.connect("http://example.com");
        }
    }
}
