package security.passthrough;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.StringReader;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.text.MessageFormat;
import java.util.StringJoiner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.naming.NamingException;
import javax.naming.Reference;
import javax.naming.ldap.BasicControl;
import javax.naming.ldap.Rdn;
import javax.naming.ldap.SortKey;

import org.springframework.http.HttpHeaders;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

/**
 * Regression samples for the value-carrying passThrough models in {@code model/java/config}.
 *
 * Each unsafe/safe pair pins one library model: the unsafe method must keep the taint
 * flowing from the request parameter through the modelled call chain into
 * {@code Runtime.exec}, the safe twin runs the identical chain over a constant and must
 * not report. The pairs exist so that a change to a passthrough slot (its name, its
 * declared value type, or its owner) is caught here instead of silently turning into a
 * false negative in the field.
 */
@RestController
@RequestMapping("/passthrough/value-flow")
public class PassthroughValueFlowSamples {

    private static final String CONSTANT = "release-notes.txt";

    // === java.lang.AbstractStringBuilder#content ===

    /** StringBuilder#append(String) -> StringBuilder#toString. */
    @GetMapping("/string-builder/unsafe")
    public void stringBuilderAppendUnsafe(@RequestParam String input) throws IOException {
        StringBuilder builder = new StringBuilder();
        builder.append("cat ");
        builder.append(input);
        Runtime.getRuntime().exec(builder.toString());
    }

    @GetMapping("/string-builder/safe")
    public void stringBuilderAppendSafe(@RequestParam String input) throws IOException {
        StringBuilder builder = new StringBuilder();
        builder.append("cat ");
        builder.append(CONSTANT);
        Runtime.getRuntime().exec(builder.toString());
    }

    /** StringBuilder#append(char[]) - the element-star carrier of the char array. */
    @GetMapping("/string-builder-chars/unsafe")
    public void stringBuilderAppendCharsUnsafe(@RequestParam String input) throws IOException {
        StringBuilder builder = new StringBuilder();
        builder.append(input.toCharArray());
        Runtime.getRuntime().exec(builder.toString());
    }

    @GetMapping("/string-builder-chars/safe")
    public void stringBuilderAppendCharsSafe(@RequestParam String input) throws IOException {
        StringBuilder builder = new StringBuilder();
        builder.append(CONSTANT.toCharArray());
        Runtime.getRuntime().exec(builder.toString());
    }

    /** StringBuffer#insert(int, String). */
    @GetMapping("/string-buffer/unsafe")
    public void stringBufferInsertUnsafe(@RequestParam String input) throws IOException {
        StringBuffer buffer = new StringBuffer("cat ");
        buffer.insert(4, input);
        Runtime.getRuntime().exec(buffer.toString());
    }

    @GetMapping("/string-buffer/safe")
    public void stringBufferInsertSafe(@RequestParam String input) throws IOException {
        StringBuffer buffer = new StringBuffer("cat ");
        buffer.insert(4, CONSTANT);
        Runtime.getRuntime().exec(buffer.toString());
    }

    // === java.lang.String#format - the argument is boxed into an Object[] element ===

    @GetMapping("/string-format/unsafe")
    public void stringFormatUnsafe(@RequestParam String input) throws IOException {
        String command = String.format("cat %s", input);
        Runtime.getRuntime().exec(command);
    }

    @GetMapping("/string-format/safe")
    public void stringFormatSafe(@RequestParam String input) throws IOException {
        String command = String.format("cat %s", CONSTANT);
        Runtime.getRuntime().exec(command);
    }

    // === java.util.StringJoiner ===

    /** The joined element must reach StringJoiner#toString. */
    @GetMapping("/string-joiner-add/unsafe")
    public void stringJoinerAddUnsafe(@RequestParam String input) throws IOException {
        StringJoiner joiner = new StringJoiner(" ");
        joiner.add("cat");
        joiner.add(input);
        Runtime.getRuntime().exec(joiner.toString());
    }

    @GetMapping("/string-joiner-add/safe")
    public void stringJoinerAddSafe(@RequestParam String input) throws IOException {
        StringJoiner joiner = new StringJoiner(" ");
        joiner.add("cat");
        joiner.add(CONSTANT);
        Runtime.getRuntime().exec(joiner.toString());
    }

    /** The delimiter itself is a carrier too - it ends up in the joined output. */
    @GetMapping("/string-joiner-delimiter/unsafe")
    public void stringJoinerDelimiterUnsafe(@RequestParam String input) throws IOException {
        StringJoiner joiner = new StringJoiner(input);
        joiner.add("cat");
        joiner.add("file");
        Runtime.getRuntime().exec(joiner.toString());
    }

    @GetMapping("/string-joiner-delimiter/safe")
    public void stringJoinerDelimiterSafe(@RequestParam String input) throws IOException {
        StringJoiner joiner = new StringJoiner(CONSTANT);
        joiner.add("cat");
        joiner.add("file");
        Runtime.getRuntime().exec(joiner.toString());
    }

    // === java.util.regex.Matcher#input ===

    /** Pattern#matcher stores the input, Matcher#group reads it back. */
    @GetMapping("/matcher-group/unsafe")
    public void matcherGroupUnsafe(@RequestParam String input) throws IOException {
        Matcher matcher = Pattern.compile("(.*)").matcher(input);
        if (matcher.find()) {
            Runtime.getRuntime().exec("cat " + matcher.group());
        }
    }

    @GetMapping("/matcher-group/safe")
    public void matcherGroupSafe(@RequestParam String input) throws IOException {
        Matcher matcher = Pattern.compile("(.*)").matcher(CONSTANT);
        if (matcher.find()) {
            Runtime.getRuntime().exec("cat " + matcher.group());
        }
    }

    /** Matcher#appendTail writes the remaining input into the target builder. */
    @GetMapping("/matcher-append-tail/unsafe")
    public void matcherAppendTailUnsafe(@RequestParam String input) throws IOException {
        Matcher matcher = Pattern.compile("^cat").matcher(input);
        StringBuffer buffer = new StringBuffer();
        matcher.appendTail(buffer);
        Runtime.getRuntime().exec(buffer.toString());
    }

    @GetMapping("/matcher-append-tail/safe")
    public void matcherAppendTailSafe(@RequestParam String input) throws IOException {
        Matcher matcher = Pattern.compile("^cat").matcher(CONSTANT);
        StringBuffer buffer = new StringBuffer();
        matcher.appendTail(buffer);
        Runtime.getRuntime().exec(buffer.toString());
    }

    // === java.text.MessageFormat#pattern ===

    @GetMapping("/message-format/unsafe")
    public void messageFormatUnsafe(@RequestParam String input) throws IOException {
        MessageFormat format = new MessageFormat(input);
        String command = format.format(new Object[] { "arg" });
        Runtime.getRuntime().exec(command);
    }

    @GetMapping("/message-format/safe")
    public void messageFormatSafe(@RequestParam String input) throws IOException {
        MessageFormat format = new MessageFormat(CONSTANT);
        String command = format.format(new Object[] { "arg" });
        Runtime.getRuntime().exec(command);
    }

    // === java.io.ByteArrayOutputStream#buffer ===

    @GetMapping("/byte-array-output-stream/unsafe")
    public void byteArrayOutputStreamUnsafe(@RequestParam String input) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        out.write(input.getBytes());
        Runtime.getRuntime().exec(new String(out.toByteArray()));
    }

    @GetMapping("/byte-array-output-stream/safe")
    public void byteArrayOutputStreamSafe(@RequestParam String input) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        out.write(CONSTANT.getBytes());
        Runtime.getRuntime().exec(new String(out.toByteArray()));
    }

    // === java.io.Reader#content ===

    @GetMapping("/string-reader/unsafe")
    public void stringReaderUnsafe(@RequestParam String input) throws IOException {
        StringReader reader = new StringReader(input);
        char[] chars = new char[64];
        reader.read(chars);
        Runtime.getRuntime().exec(new String(chars));
    }

    @GetMapping("/string-reader/safe")
    public void stringReaderSafe(@RequestParam String input) throws IOException {
        StringReader reader = new StringReader(CONSTANT);
        char[] chars = new char[64];
        reader.read(chars);
        Runtime.getRuntime().exec(new String(chars));
    }

    // === java.nio buffers ===

    @GetMapping("/byte-buffer/unsafe")
    public void byteBufferUnsafe(@RequestParam String input) throws IOException {
        ByteBuffer buffer = ByteBuffer.allocate(256);
        buffer.put(input.getBytes());
        Runtime.getRuntime().exec(new String(buffer.array()));
    }

    @GetMapping("/byte-buffer/safe")
    public void byteBufferSafe(@RequestParam String input) throws IOException {
        ByteBuffer buffer = ByteBuffer.allocate(256);
        buffer.put(CONSTANT.getBytes());
        Runtime.getRuntime().exec(new String(buffer.array()));
    }

    @GetMapping("/char-buffer/unsafe")
    public void charBufferUnsafe(@RequestParam String input) throws IOException {
        CharBuffer buffer = CharBuffer.allocate(256);
        buffer.put(input);
        Runtime.getRuntime().exec(buffer.flip().toString());
    }

    @GetMapping("/char-buffer/safe")
    public void charBufferSafe(@RequestParam String input) throws IOException {
        CharBuffer buffer = CharBuffer.allocate(256);
        buffer.put(CONSTANT);
        Runtime.getRuntime().exec(buffer.flip().toString());
    }

    // === models that fill a caller-supplied buffer (arg, not result) ===

    /** String#getChars(int,int,char[],int) copies into the destination array. */
    @GetMapping("/string-get-chars/unsafe")
    public void stringGetCharsUnsafe(@RequestParam String input) throws IOException {
        char[] chars = new char[input.length()];
        input.getChars(0, input.length(), chars, 0);
        Runtime.getRuntime().exec(new String(chars));
    }

    @GetMapping("/string-get-chars/safe")
    public void stringGetCharsSafe(@RequestParam String input) throws IOException {
        char[] chars = new char[CONSTANT.length()];
        CONSTANT.getChars(0, CONSTANT.length(), chars, 0);
        Runtime.getRuntime().exec(new String(chars));
    }

    /** ByteBuffer#get(byte[]) drains the buffer into the destination array. */
    @GetMapping("/byte-buffer-get/unsafe")
    public void byteBufferGetUnsafe(@RequestParam String input) throws IOException {
        ByteBuffer buffer = ByteBuffer.wrap(input.getBytes());
        byte[] drained = new byte[input.length()];
        buffer.get(drained);
        Runtime.getRuntime().exec(new String(drained));
    }

    @GetMapping("/byte-buffer-get/safe")
    public void byteBufferGetSafe(@RequestParam String input) throws IOException {
        ByteBuffer buffer = ByteBuffer.wrap(CONSTANT.getBytes());
        byte[] drained = new byte[CONSTANT.length()];
        buffer.get(drained);
        Runtime.getRuntime().exec(new String(drained));
    }

    /** CharBuffer#get(char[]) does the same for chars. */
    @GetMapping("/char-buffer-get/unsafe")
    public void charBufferGetUnsafe(@RequestParam String input) throws IOException {
        CharBuffer buffer = CharBuffer.wrap(input);
        char[] drained = new char[input.length()];
        buffer.get(drained);
        Runtime.getRuntime().exec(new String(drained));
    }

    @GetMapping("/char-buffer-get/safe")
    public void charBufferGetSafe(@RequestParam String input) throws IOException {
        CharBuffer buffer = CharBuffer.wrap(CONSTANT);
        char[] drained = new char[CONSTANT.length()];
        buffer.get(drained);
        Runtime.getRuntime().exec(new String(drained));
    }

    // === javax.naming slots ===

    /** BasicControl stores the control OID, getID reads it back. */
    @GetMapping("/ldap-control-id/unsafe")
    public void basicControlIdUnsafe(@RequestParam String input) throws IOException {
        BasicControl control = new BasicControl(input);
        Runtime.getRuntime().exec("ldapsearch " + control.getID());
    }

    @GetMapping("/ldap-control-id/safe")
    public void basicControlIdSafe(@RequestParam String input) throws IOException {
        BasicControl control = new BasicControl(CONSTANT);
        Runtime.getRuntime().exec("ldapsearch " + control.getID());
    }

    /** Rdn keeps the attribute type in its own slot. */
    @GetMapping("/ldap-rdn-type/unsafe")
    public void rdnTypeUnsafe(@RequestParam String input) throws IOException, NamingException {
        Rdn rdn = new Rdn(input, "value");
        Runtime.getRuntime().exec("ldapsearch " + rdn.getType());
    }

    @GetMapping("/ldap-rdn-type/safe")
    public void rdnTypeSafe(@RequestParam String input) throws IOException, NamingException {
        Rdn rdn = new Rdn(CONSTANT, "value");
        Runtime.getRuntime().exec("ldapsearch " + rdn.getType());
    }

    /** SortKey keeps the matching rule id apart from the attribute id. */
    @GetMapping("/ldap-sort-key/unsafe")
    public void sortKeyMatchingRuleUnsafe(@RequestParam String input) throws IOException {
        SortKey key = new SortKey("cn", true, input);
        Runtime.getRuntime().exec("ldapsearch " + key.getMatchingRuleID());
    }

    @GetMapping("/ldap-sort-key/safe")
    public void sortKeyMatchingRuleSafe(@RequestParam String input) throws IOException {
        SortKey key = new SortKey("cn", true, CONSTANT);
        Runtime.getRuntime().exec("ldapsearch " + key.getMatchingRuleID());
    }

    /** Reference keeps the class name in its own slot. */
    @GetMapping("/naming-reference/unsafe")
    public void referenceClassNameUnsafe(@RequestParam String input) throws IOException {
        Reference reference = new Reference(input);
        Runtime.getRuntime().exec("jndi " + reference.getClassName());
    }

    @GetMapping("/naming-reference/safe")
    public void referenceClassNameSafe(@RequestParam String input) throws IOException {
        Reference reference = new Reference(CONSTANT);
        Runtime.getRuntime().exec("jndi " + reference.getClassName());
    }

    // === org.springframework.http.HttpHeaders ===

    @GetMapping("/http-headers/unsafe")
    public void httpHeadersUnsafe(@RequestParam String input) throws IOException {
        HttpHeaders headers = new HttpHeaders();
        headers.set("X-Command", input);
        Runtime.getRuntime().exec("cat " + headers.getFirst("X-Command"));
    }

    @GetMapping("/http-headers/safe")
    public void httpHeadersSafe(@RequestParam String input) throws IOException {
        HttpHeaders headers = new HttpHeaders();
        headers.set("X-Command", CONSTANT);
        Runtime.getRuntime().exec("cat " + headers.getFirst("X-Command"));
    }
}
