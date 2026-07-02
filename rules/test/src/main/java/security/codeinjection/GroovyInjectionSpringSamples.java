package security.codeinjection;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

import groovy.lang.GroovyShell;

/**
 * Spring MVC samples for groovy-injection-in-spring.
 */
public class GroovyInjectionSpringSamples {

    @RestController
    public static class UnsafeGroovyController {

        @GetMapping("/groovy-injection-in-spring/unsafe")
        public String unsafeGroovy(@RequestParam("script") String script) {
            GroovyShell shell = new GroovyShell();

            // VULNERABLE: directly evaluates attacker-controlled script code
            Object result = shell.evaluate(script);

            return String.valueOf(result);
        }
    }

    @RestController
    public static class SafeGroovyController {

        @GetMapping("/groovy-injection-in-spring/safe")
        public String safeGroovy(@RequestParam(value = "action", required = false) String action) {
            // Safer pattern: map user-controlled input to a fixed set of allowed operations,
            // without evaluating arbitrary Groovy code.
            if ("ping".equals(action)) {
                return "pong";
            }
            if ("version".equals(action)) {
                return "1.0";
            }
            return "unsupported";
        }
    }
}
