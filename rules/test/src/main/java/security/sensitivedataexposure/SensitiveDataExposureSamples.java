package security.sensitivedataexposure;


import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.http.Cookie;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.ServerSocket;
import org.springframework.http.ResponseCookie;
import org.springframework.web.util.CookieGenerator;

/**
 * Samples for sensitive-data-exposure rules.
 */
public class SensitiveDataExposureSamples {

    // cookie-issecure-false

    @org.springframework.web.bind.annotation.GetMapping("/insecureCookie")
    public void insecureSessionCookie(HttpServletResponse response) {
        // VULNERABLE: create a cookie without setting Secure, allowing cleartext transport
        Cookie session = new Cookie("SESSIONID", "sensitive-session-id");
        response.addCookie(session);
    }

    @org.springframework.web.bind.annotation.GetMapping("/secureCookie")
    public void secureSessionCookie(HttpServletResponse response) {
        Cookie session = new Cookie("SESSIONID", "sensitive-session-id");
        // SAFE: explicitly mark cookie as Secure (and typically HttpOnly, but rule focuses on Secure)
        session.setSecure(true);
        response.addCookie(session);
    }

    @org.springframework.web.bind.annotation.GetMapping("/secureEmptyCookie")
    public void secureEmptySessionCookie(HttpServletResponse response) {
        Cookie session = new Cookie("SESSIONID", "sensitive-session-id");
        // SAFE: cookie value is empty, no sensitive data to expose
        session.setValue("");
        response.addCookie(session);
    }

    public void explicitSetSecureFalse(HttpServletResponse response) {
        Cookie cookie = new Cookie("TOKEN", "value");
        // VULNERABLE: explicitly setting Secure to false
        cookie.setSecure(false);
        response.addCookie(cookie);
    }

    public void springResponseCookieSecureFalse() {
        // VULNERABLE: explicitly setting secure(false) on ResponseCookie builder
        ResponseCookie.ResponseCookieBuilder builder = ResponseCookie.from("TOKEN", "value");
        builder.secure(false);
    }

    public void springResponseCookieSecureTrue() {
        // SAFE: setting secure(true) on ResponseCookie builder
        ResponseCookie.ResponseCookieBuilder builder = ResponseCookie.from("TOKEN", "value");
        builder.secure(true);
    }

    public void cookieGeneratorWithoutSecure(HttpServletResponse response) {
        // VULNERABLE: CookieGenerator without setCookieSecure(true)
        CookieGenerator gen = new CookieGenerator();
        gen.setCookieName("TOKEN");
        gen.addCookie(response, "value");
    }

    public void cookieGeneratorWithSecure(HttpServletResponse response) {
        // SAFE: CookieGenerator with setCookieSecure(true)
        CookieGenerator gen = new CookieGenerator();
        gen.setCookieName("TOKEN");
        gen.setCookieSecure(true);
        gen.addCookie(response, "value");
    }

    public void cookieGeneratorExplicitSecureFalse(HttpServletResponse response) {
        // VULNERABLE: explicitly setting setCookieSecure(false)
        CookieGenerator gen = new CookieGenerator();
        gen.setCookieSecure(false);
        gen.addCookie(response, "value");
    }

    public void rawSetCookieHeaderWithoutSecure(HttpServletResponse response) {
        // VULNERABLE: raw Set-Cookie header without Secure flag
        response.addHeader("Set-Cookie", "TOKEN=value; HttpOnly; Path=/");
    }

    public void rawSetCookieHeaderWithSecure(HttpServletResponse response) {
        // SAFE: raw Set-Cookie header with Secure flag
        response.addHeader("Set-Cookie", "TOKEN=value; HttpOnly; Secure; Path=/");
    }

    // unencrypted-socket

    public Socket createUnencryptedSocket(String host, int port) throws IOException {
        // VULNERABLE: plain Socket, no TLS
        return new Socket(host, port);
    }

    public javax.net.ssl.SSLSocket createEncryptedSocket(String host, int port) throws Exception {
        javax.net.ssl.SSLSocketFactory factory = (javax.net.ssl.SSLSocketFactory) javax.net.ssl.SSLSocketFactory.getDefault();
        return (javax.net.ssl.SSLSocket) factory.createSocket(host, port);
    }

    public ServerSocket createUnencryptedServerSocket(int port) throws IOException {
        // VULNERABLE: plain ServerSocket, no TLS
        return new ServerSocket(port);
    }

    public javax.net.ssl.SSLServerSocket createEncryptedServerSocket(int port) throws Exception {
        javax.net.ssl.SSLServerSocketFactory factory = (javax.net.ssl.SSLServerSocketFactory) javax.net.ssl.SSLServerSocketFactory.getDefault();
        return (javax.net.ssl.SSLServerSocket) factory.createServerSocket(port);
    }

    // url-rewriting

    public static class UrlRewritingController {

        @org.springframework.web.bind.annotation.GetMapping("/track")
        public void track(HttpServletRequest request, HttpServletResponse response) throws IOException {
            String product = request.getParameter("id");
            String target = "https://partner.example.com/track?product=" + product;
            // VULNERABLE: encodeRedirectURL may append ;jsessionid, exposing the session id
            String encoded = response.encodeRedirectURL(target);
            response.sendRedirect(encoded);
        }

        @org.springframework.web.bind.annotation.GetMapping("/trackSafe")
        public void trackSafe(HttpServletRequest request, HttpServletResponse response) throws IOException {
            String product = request.getParameter("id");
            String target = "https://partner.example.com/track?product=" + product;
            // SAFE: do not call encodeRedirectURL for external HTTPS URLs
            response.sendRedirect(target);
        }
    }

    // file-disclosure-request-dispatcher (taint join rule via untrusted path)

    public static class FileDisclosureServlet extends HttpServlet {

        @Override
        protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
            String path = request.getParameter("view");
            // VULNERABLE: pass user-controlled path directly to RequestDispatcher
            RequestDispatcher dispatcher = request.getRequestDispatcher(path);
            dispatcher.forward(request, response);
        }

        protected void doGetSafe(HttpServletRequest request, HttpServletResponse response) throws IOException {
            String key = request.getParameter("view");
            String safePath;
            if ("home".equals(key)) {
                safePath = "/WEB-INF/views/home.jsp";
            } else if ("profile".equals(key)) {
                safePath = "/WEB-INF/views/profile.jsp";
            } else {
                safePath = "/WEB-INF/views/error.jsp";
            }
            // SAFE: use redirect with a controlled, server-side selected path
            response.sendRedirect(safePath);
        }

        protected void doGetFixedDispatcher(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
            // SAFE: the dispatcher path is constant even though request and response are passed to include
            RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/views/home.jsp");
            dispatcher.include(request, response);
        }
    }

    // jsp-file-disclosure (taint join rule via ModelAndView / view name)

    public static class JspFileDisclosureController {

        @org.springframework.web.bind.annotation.RequestMapping(value = "/mvc", method = org.springframework.web.bind.annotation.RequestMethod.GET)
        public org.springframework.web.servlet.ModelAndView mvcVulnerable(HttpServletRequest request, HttpServletResponse response) {
            String viewName = request.getParameter("view");
            // VULNERABLE: untrusted view name used directly
            return new org.springframework.web.servlet.ModelAndView(viewName);
        }

        @org.springframework.web.bind.annotation.RequestMapping(value = "/mvcSafe", method = org.springframework.web.bind.annotation.RequestMethod.GET)
        public org.springframework.web.servlet.ModelAndView mvcSafe(HttpServletRequest request, HttpServletResponse response) {
            String key = request.getParameter("view");
            String resolvedView;
            if ("home".equals(key)) {
                resolvedView = "home";
            } else if ("profile".equals(key)) {
                resolvedView = "profile";
            } else {
                resolvedView = "error";
            }
            // SAFE: view name is resolved via lookup, not directly controlled by user-supplied path
            return new org.springframework.web.servlet.ModelAndView(resolvedView);
        }
    }

    // stacktrace-printing-in-error-message

    public void printStackTraceToStdout(Exception e) {
        // VULNERABLE: prints stack trace directly, potentially exposing sensitive data
        e.printStackTrace();
    }

    public void logStackTraceSafely(Exception e, PrintWriter log) {
        // SAFE: write a generic error message and avoid exposing internal details
        log.println("An error occurred. Please contact support with the request ID.");
        // Stack trace would typically be logged to a protected log instead of stdout; omitted here.
    }
}
