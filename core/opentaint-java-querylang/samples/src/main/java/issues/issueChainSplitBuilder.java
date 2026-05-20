package issues;

import base.RuleSample;
import base.RuleSet;
import issues.iChain.HttpClient;
import issues.iChain.HttpRequest;
import issues.iChain.Source;
import issues.iChain.URI;

/**
 * Working counterpart of {@link issueChain}: identical chained-builder
 * source, but the sink rule binds the static {@code newBuilder()} call to
 * its own metavariable in a separate {@code pattern-inside}
 * ({@code $NEW_BUILDER = ...newBuilder();}) before matching
 * {@code $BUILDER = $NEW_BUILDER.uri($URL)}.
 *
 * <p>The fluent chain {@code newBuilder().uri(URI.create(t)).GET().build()}
 * is matched call-by-call, so the static-method receiver no longer has to
 * appear nested inside the {@code .uri(...)} pattern (the form that fails
 * in {@link issueChain}). See {@code issueChainSplitBuilder.yaml}.
 */
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
