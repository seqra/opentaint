package security.xss;

import java.io.IOException;

import javax.servlet.http.HttpServletResponse;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

/**
 * Spring MVC samples for XSS via HttpServletResponse sinks
 * (sendError and getOutputStream).
 */
public class XssServletSinkSpringSamples {

    // ── HttpServletResponse.sendError ───────────────────────────────────

    @RestController
    @RequestMapping("/xss-servlet-sink-in-spring")
    public static class UnsafeSendErrorController {

        @GetMapping("/send-error")
        public void unsafeSendError(@RequestParam("msg") String msg,
                                    HttpServletResponse response) throws IOException {
            // VULNERABLE: user-controlled message in HTTP error response
            response.sendError(500, msg);
        }
    }

    // ── HttpServletResponse.sendError (multiline form) ──────────────────

    @RestController
    @RequestMapping("/xss-servlet-sink-in-spring")
    public static class UnsafeSendErrorMultilineController {

        @GetMapping("/send-error-multiline")
        public void unsafeSendErrorMultiline(@RequestParam("msg") String msg,
                                             HttpServletResponse response) throws IOException {
            // VULNERABLE: user-controlled message in HTTP error response (multiline)
            String errorMsg = "Error: " + msg;
            response.sendError(
                    HttpServletResponse.SC_INTERNAL_SERVER_ERROR,
                    errorMsg);
        }
    }

    // ── HttpServletResponse.getOutputStream().write ─────────────────────

    @RestController
    @RequestMapping("/xss-servlet-sink-in-spring")
    public static class UnsafeOutputStreamWriteController {

        @GetMapping("/output-stream-write")
        public void unsafeOutputStreamWrite(@RequestParam("data") String data,
                                            HttpServletResponse response) throws IOException {
            response.setContentType("text/html;charset=UTF-8");
            // VULNERABLE: user-controlled data written directly to response output stream
            response.getOutputStream().write(data.getBytes());
        }
    }
}
