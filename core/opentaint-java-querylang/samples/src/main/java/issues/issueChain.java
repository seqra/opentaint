package issues;

import base.RuleSample;
import base.RuleSet;
import issues.iChain.HttpClient;
import issues.iChain.HttpRequest;
import issues.iChain.Source;
import issues.iChain.URI;

@RuleSet("issues/issueChain.yaml")
public abstract class issueChain implements RuleSample {

    // Carries real taint, but the chain pattern's nested static receiver never
    // binds, so the rule legitimately does not fire — recorded as a Negative case.
    static class NegativeTaintIntendedNonMatch extends issueChain {
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
