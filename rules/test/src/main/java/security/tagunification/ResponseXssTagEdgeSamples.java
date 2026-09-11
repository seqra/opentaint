package security.tagunification;

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;

import javax.servlet.ServletOutputStream;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.springframework.http.MediaType;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.util.HtmlUtils;

public class ResponseXssTagEdgeSamples {

    @RestController
    public static class StoredServletResponseController {

        @GetMapping("/tag-unification/response-writer")
        public void springParameterToStoredWriter(
                @RequestParam String value,
                HttpServletResponse response) throws IOException {
            PrintWriter writer = response.getWriter();
            writer.write(value);
        }

        @GetMapping("/tag-unification/response-stream")
        public void springParameterToStoredOutputStream(
                @RequestParam String value,
                HttpServletResponse response) throws IOException {
            ServletOutputStream stream = response.getOutputStream();
            stream.write(value.getBytes(StandardCharsets.UTF_8));
        }

        @GetMapping("/tag-unification/html-writer")
        public void springParameterToStoredHtmlWriter(
                @RequestParam String value,
                HttpServletResponse response) throws IOException {
            response.setContentType("text/html;charset=UTF-8");
            PrintWriter writer = response.getWriter();
            writer.write("<p>" + value + "</p>");
        }

        @GetMapping("/tag-unification/html-stream")
        public void springParameterToStoredHtmlOutputStream(
                @RequestParam String value,
                HttpServletResponse response) throws IOException {
            response.setContentType("text/html;charset=UTF-8");
            ServletOutputStream stream = response.getOutputStream();
            stream.write(("<p>" + value + "</p>").getBytes(StandardCharsets.UTF_8));
        }

        @GetMapping("/tag-unification/escaped-html")
        public void springParameterToEscapedHtml(
                @RequestParam String value,
                HttpServletResponse response) throws IOException {
            response.setContentType("text/html;charset=UTF-8");
            PrintWriter writer = response.getWriter();
            writer.write("<p>" + HtmlUtils.htmlEscape(value) + "</p>");
        }
    }

    @RestController
    public static class SpringResponseEntityController {

        @GetMapping(value = "/tag-unification/servlet-source-html", produces = MediaType.TEXT_HTML_VALUE)
        public ResponseEntity<String> requestObjectToSpringHtmlResponse(
                HttpServletRequest request) {
            String value = request.getParameter("value");
            return ResponseEntity.ok()
                    .contentType(MediaType.TEXT_HTML)
                    .body("<p>" + value + "</p>");
        }

        @GetMapping(value = "/tag-unification/json-dto", produces = MediaType.APPLICATION_JSON_VALUE)
        public ResponseEntity<Payload> springParameterToJsonDto(@RequestParam String value) {
            return ResponseEntity.ok(new Payload(value));
        }
    }

    public static class Payload {
        public final String value;

        public Payload(String value) {
            this.value = value;
        }
    }
}
