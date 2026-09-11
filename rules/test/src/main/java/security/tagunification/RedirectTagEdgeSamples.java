package security.tagunification;

import java.io.IOException;

import javax.servlet.http.HttpServletResponse;

import org.springframework.stereotype.Controller;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.servlet.view.RedirectView;

/**
 * Cross-framework samples for redirect source and sink tag unification.
 */
public final class RedirectTagEdgeSamples {

    private RedirectTagEdgeSamples() {
    }

    @Controller
    public static final class SpringParameterToServletResponse {

        @GetMapping("/tag-unification/redirect")
        public void springParamToServletRedirect(
                @RequestParam("target") String target,
                HttpServletResponse response) throws IOException {
            response.sendRedirect(target);
        }

        @GetMapping("/tag-unification/safe-redirect")
        public void springParamToConstantServletRedirect(
                @RequestParam("ignored") String ignored,
                HttpServletResponse response) throws IOException {
            response.sendRedirect("/home");
        }
    }

    @Controller
    public static final class CustomSourceToSpringRedirect {

        @GetMapping("/tag-unification/custom-source-redirect")
        public RedirectView customSourceToSpringRedirect() {
            String target = CustomBoundary.read();
            return new RedirectView(target);
        }
    }

    public static final class CustomBoundary {

        private CustomBoundary() {
        }

        public static String read() {
            return "external";
        }
    }
}
