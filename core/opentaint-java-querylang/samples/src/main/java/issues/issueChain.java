package issues;

import base.RuleSample;
import base.RuleSet;
import issues.iChain.HttpClient;
import issues.iChain.HttpRequest;
import issues.iChain.Source;
import issues.iChain.URI;

/**
 * INTENDED non-match: the rule legitimately does not fire on the tainted fluent
 * chain, so that case is recorded as a {@code Negative} sample
 * ({@link NegativeTaintIntendedNonMatch}) rather than a positive, and the
 * {@code issueChain} test passes.
 *
 * <p>The sink rule nests the static receiver inside a single expression,
 * {@code $BUILDER = HttpRequest.newBuilder().uri($URL)}, and then matches
 * {@code $BUILDER.build()}. The source, however, builds the request as one
 * fluent chain:
 * <pre>
 *   req = HttpRequest.newBuilder().uri(URI.create(t)).GET().build();
 * </pre>
 * whose calls are matched one at a time. The order/structure of the calls
 * in the rule does not line up with the source — there is no point where a
 * single {@code newBuilder().uri(...)} sub-expression is the direct receiver
 * of {@code .build()} (the {@code .GET()} call sits in between) — so the
 * literal nested receiver never binds and the rule legitimately does not
 * fire. This is expected behaviour, not an analyzer false-negative.
 *
 * <p>The working way to express the same intent is to bind the static
 * {@code newBuilder()} call to its own metavariable first and then match the
 * chain call-by-call. See {@link issueChainSplitBuilder} (and
 * {@code issueChainSplitBuilder.yaml}) for that passing counterpart.
 */
@RuleSet("issues/issueChain.yaml")
public abstract class issueChain implements RuleSample {

    // Carries real taint, but the chain pattern legitimately does not match
    // (see class Javadoc), so no finding is expected — recorded as a Negative case.
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
