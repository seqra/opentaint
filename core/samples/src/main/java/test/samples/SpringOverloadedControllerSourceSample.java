package test.samples;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;

@RestController
public final class SpringOverloadedControllerSourceSample {
    @GetMapping
    public void list(FirstRequest request) {
        sinkFirst(request.getValue());
    }

    @GetMapping
    public void list(SecondRequest request) {
        sinkSecond(request.getValue());
    }

    public static void sinkFirst(String value) {
    }

    public static void sinkSecond(String value) {
    }

    public static final class FirstRequest {
        private String value;

        public String getValue() {
            return value;
        }
    }

    public static final class SecondRequest {
        private String value;

        public String getValue() {
            return value;
        }
    }
}
