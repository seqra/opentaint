package issues;

import base.RuleSample;
import base.RuleSet;
import issues.iChain.HttpClient;
import issues.iChain.HttpRequest;
import issues.iChain.Source;
import issues.iChain.URI;

@RuleSet("issues/issueChain.yaml")
public abstract class issueChain implements RuleSample {

    // Carries real taint, but the rule's sub-pattern order (URL bound before the
    // builder) doesn't line up with the code's call order (builder created first),
    // so the sink is unreachable and the rule does not fire — a Negative case.
    static class NegativeTaintOrderSensitive extends issueChain {
        @Override
        public void entrypoint() {
            String t = Source.taint();
            HttpRequest req = HttpRequest.newBuilder()
                    .uri(URI.create(t))
                    .GET()
                    .build();
            HttpClient client = HttpClient.newHttpClient();
            client.send(req);
        }
    }

    static class NegativeTaint extends issueChain {
        @Override
        public void entrypoint() {
            HttpRequest req = HttpRequest.newBuilder()
                    .uri(URI.create("https://example.com"))
                    .GET()
                    .build();
            HttpClient client = HttpClient.newHttpClient();
            client.send(req);
        }
    }
}
