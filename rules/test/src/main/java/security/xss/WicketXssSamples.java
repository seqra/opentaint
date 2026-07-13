package security.xss;

import org.apache.wicket.markup.html.WebPage;
import org.apache.wicket.markup.html.basic.Label;
import org.apache.wicket.model.Model;

/**
 * Samples for wicket-xss.
 */
public class WicketXssSamples {

    /**
     * Wicket page that disables string escaping, which can lead to XSS when used with
     * user-controlled input.
     */
    public static class UnsafeWicketPage extends WebPage {

        public UnsafeWicketPage(String userSuppliedContent) {
            Label label = new Label("message", Model.of(userSuppliedContent));

            // VULNERABLE: disable escaping so user input is rendered as raw HTML/JS.
            label.setEscapeModelStrings(false);

            add(label);
        }
    }

    /**
     * Wicket page that keeps string escaping enabled, which is the recommended safe default.
     */
    public static class SafeWicketPage extends WebPage {

        public SafeWicketPage(String userSuppliedContent) {
            Label label = new Label("message", Model.of(userSuppliedContent));

            // SAFE: either keep the default (true) or set it explicitly.
            label.setEscapeModelStrings(true);

            add(label);
        }
    }
}
