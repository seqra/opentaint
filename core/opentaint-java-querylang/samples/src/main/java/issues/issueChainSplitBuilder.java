package issues;

import base.RuleSample;
import base.RuleSet;
import issues.iChain.HttpClient;
import issues.iChain.HttpRequest;
import issues.iChain.Source;
import issues.iChain.URI;

@RuleSet("issues/issueChainSplitBuilder.yaml")
public abstract class issueChainSplitBuilder implements RuleSample {

    static class PositiveTaint extends issueChainSplitBuilder {
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

    static class NegativeTaint extends issueChainSplitBuilder {
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
