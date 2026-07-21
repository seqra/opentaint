package test.samples;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;

/** Adds the shared Spring component state present in the full Stirling application. */
@RestController
public final class StirlingTraceResolutionRegressionPolluter {
    @Autowired private ApplicationProperties applicationProperties;

    @GetMapping
    public void pollute(ApplicationProperties request) {
        this.applicationProperties = request;
    }

    public static final class ApplicationProperties {
        private String value;

        public String getValue() {
            return value;
        }
    }
}
