package security.strings;

import java.io.IOException;
import java.io.PrintWriter;
import java.text.Normalizer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.springframework.stereotype.Controller;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.ResponseBody;

/**
 * Samples for strings-related rules in {@code java/security/strings.yaml}.
 */
public class StringsSamples {

    // string-normalize-after-validation

    public String normalizeAfterValidation(String input) throws Exception {
        // Compile regex pattern looking for < or > characters
        Pattern pattern = Pattern.compile("[<>]");
        // Validate the raw input first
        Matcher matcher = pattern.matcher(input);
        if (matcher.find()) {
            throw new Exception("found banned characters in input");
        }
        // VULNERABLE: normalize only after validation
        return Normalizer.normalize(input, Normalizer.Form.NFKC);
    }

    public String normalizeBeforeValidation(String input) throws Exception {
        // SAFE: normalize before validation
        String userInput = Normalizer.normalize(input, Normalizer.Form.NFKC);
        Pattern pattern = Pattern.compile("[<>]");
        Matcher matcher = pattern.matcher(userInput);
        if (matcher.find()) {
            throw new Exception("found banned characters in input");
        }
        return userInput;
    }

    // format-string-external-manipulation (join rule via servlet untrusted source)

    @WebServlet("/strings/format/servlet")
    public static class FormatStringServlet extends HttpServlet {

        @Override
        protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
            String userFormat = request.getParameter("fmt");
            String value = request.getParameter("value");

            // VULNERABLE: user-controlled format string
            String formatted = String.format(userFormat, value);

            PrintWriter writer = response.getWriter();
            writer.println(formatted);
        }

        protected void doGetSafe(HttpServletRequest request, HttpServletResponse response) throws IOException {
            String value = request.getParameter("value");

            // SAFE: hardcoded format string, user input only as parameter
            String formatted = String.format("Value: %s", value);

            PrintWriter writer = response.getWriter();
            writer.println(formatted);
        }
    }

    // format-string-external-manipulation (join rule via Spring untrusted source)

    @Controller
    @RequestMapping("/strings/format")
    public static class FormatStringSpringController {

        @GetMapping("/unsafe")
        @ResponseBody
        public String unsafe(@RequestParam("fmt") String fmt,
                             @RequestParam("value") String value) {
            // VULNERABLE: user-controlled format string
            return String.format(fmt, value);
        }

        @GetMapping("/safe")
        @ResponseBody
        public String safe(@RequestParam("value") String value) {
            // SAFE: use a hardcoded format string, user input as data only
            return String.format("Value: %s", value);
        }
    }
}
