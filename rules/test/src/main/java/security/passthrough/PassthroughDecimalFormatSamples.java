package security.passthrough;

import java.io.IOException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.text.DecimalFormat;
import java.text.DecimalFormatSymbols;
import java.util.Currency;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

/** Passthrough regressions using the existing crypto and command-injection rules. */
@RestController
public class PassthroughDecimalFormatSamples {
    // Rebuild the digest buffer from the getter: the original digest's taint
    // cannot reach the existing hex-conversion sink without crossing that property.
    public String multiplier(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setMultiplier(digest[0]);
        digest = new byte[] { (byte) format.getMultiplier() };
        return Integer.toHexString(digest[0]);
    }

    public String groupingSize(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setGroupingSize(digest[0]);
        digest = new byte[] { (byte) format.getGroupingSize() };
        return Integer.toHexString(digest[0]);
    }

    public String maximumIntegerDigits(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setMaximumIntegerDigits(digest[0]);
        digest = new byte[] { (byte) format.getMaximumIntegerDigits() };
        return Integer.toHexString(digest[0]);
    }

    public String minimumIntegerDigits(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setMinimumIntegerDigits(digest[0]);
        digest = new byte[] { (byte) format.getMinimumIntegerDigits() };
        return Integer.toHexString(digest[0]);
    }

    public String maximumFractionDigits(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setMaximumFractionDigits(digest[0]);
        digest = new byte[] { (byte) format.getMaximumFractionDigits() };
        return Integer.toHexString(digest[0]);
    }

    public String minimumFractionDigits(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setMinimumFractionDigits(digest[0]);
        digest = new byte[] { (byte) format.getMinimumFractionDigits() };
        return Integer.toHexString(digest[0]);
    }

    public String clampMaximumIntegerDigits(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setMaximumIntegerDigits(digest[0]);
        digest = new byte[] { (byte) format.getMinimumIntegerDigits() };
        return Integer.toHexString(digest[0]);
    }

    public String clampMinimumIntegerDigits(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setMaximumIntegerDigits(0);
        format.setMinimumIntegerDigits(digest[0]);
        digest = new byte[] { (byte) format.getMaximumIntegerDigits() };
        return Integer.toHexString(digest[0]);
    }

    public String clampMaximumFractionDigits(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setMaximumFractionDigits(digest[0]);
        digest = new byte[] { (byte) format.getMinimumFractionDigits() };
        return Integer.toHexString(digest[0]);
    }

    public String clampMinimumFractionDigits(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setMinimumFractionDigits(digest[0]);
        digest = new byte[] { (byte) format.getMaximumFractionDigits() };
        return Integer.toHexString(digest[0]);
    }

    public String multiplierDoesNotSetGrouping(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setMultiplier(digest[0]);
        digest = new byte[] { (byte) format.getGroupingSize() };
        return Integer.toHexString(digest[0]);
    }

    public String groupingDoesNotSetDigits(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setGroupingSize(digest[0]);
        digest = new byte[] { (byte) format.getMaximumIntegerDigits() };
        return Integer.toHexString(digest[0]);
    }

    public String integerDoesNotSetFraction(byte[] input) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        byte[] digest = md.digest(input);
        DecimalFormat format = new DecimalFormat();
        format.setMaximumIntegerDigits(digest[0]);
        digest = new byte[] { (byte) format.getMaximumFractionDigits() };
        return Integer.toHexString(digest[0]);
    }

    @GetMapping("/passthrough/decimal-format/setCurrencyTogetCurrency")
    public void setCurrencyTogetCurrency(@RequestParam Currency value) throws IOException {
        DecimalFormatSymbols symbols = new DecimalFormatSymbols();
        symbols.setCurrency(value);
        Runtime.getRuntime().exec(symbols.getCurrency().toString());
    }

    @GetMapping("/passthrough/decimal-format/setCurrencyTogetCurrencySymbol")
    public void setCurrencyTogetCurrencySymbol(@RequestParam Currency value) throws IOException {
        DecimalFormatSymbols symbols = new DecimalFormatSymbols();
        symbols.setCurrency(value);
        Runtime.getRuntime().exec(symbols.getCurrencySymbol());
    }

    @GetMapping("/passthrough/decimal-format/setCurrencyTogetInternationalCurrencySymbol")
    public void setCurrencyTogetInternationalCurrencySymbol(@RequestParam Currency value) throws IOException {
        DecimalFormatSymbols symbols = new DecimalFormatSymbols();
        symbols.setCurrency(value);
        Runtime.getRuntime().exec(symbols.getInternationalCurrencySymbol());
    }

    @GetMapping("/passthrough/decimal-format/setInternationalCurrencySymbolTogetCurrency")
    public void setInternationalCurrencySymbolTogetCurrency(@RequestParam String value) throws IOException {
        DecimalFormatSymbols symbols = new DecimalFormatSymbols();
        symbols.setInternationalCurrencySymbol(value);
        Runtime.getRuntime().exec(symbols.getCurrency().toString());
    }

    @GetMapping("/passthrough/decimal-format/setInternationalCurrencySymbolTogetCurrencySymbol")
    public void setInternationalCurrencySymbolTogetCurrencySymbol(@RequestParam String value) throws IOException {
        DecimalFormatSymbols symbols = new DecimalFormatSymbols();
        symbols.setInternationalCurrencySymbol(value);
        Runtime.getRuntime().exec(symbols.getCurrencySymbol());
    }

    @GetMapping("/passthrough/decimal-format/setInternationalCurrencySymbolTogetInternationalCurrencySymbol")
    public void setInternationalCurrencySymbolTogetInternationalCurrencySymbol(@RequestParam String value) throws IOException {
        DecimalFormatSymbols symbols = new DecimalFormatSymbols();
        symbols.setInternationalCurrencySymbol(value);
        Runtime.getRuntime().exec(symbols.getInternationalCurrencySymbol());
    }

    @GetMapping("/passthrough/decimal-format/formatCurrencyTogetCurrencySymbol")
    public void formatCurrencyTogetCurrencySymbol(@RequestParam Currency value) throws IOException {
        DecimalFormat format = new DecimalFormat();
        format.setCurrency(value);
        Runtime.getRuntime().exec(format.getDecimalFormatSymbols().getCurrencySymbol());
    }

    @GetMapping("/passthrough/decimal-format/formatCurrencyTogetInternationalCurrencySymbol")
    public void formatCurrencyTogetInternationalCurrencySymbol(@RequestParam Currency value) throws IOException {
        DecimalFormat format = new DecimalFormat();
        format.setCurrency(value);
        Runtime.getRuntime().exec(format.getDecimalFormatSymbols().getInternationalCurrencySymbol());
    }

    @GetMapping("/passthrough/decimal-format/currencyDoesNotSetNaN")
    public void currencyDoesNotSetNaN(@RequestParam Currency value) throws IOException {
        DecimalFormatSymbols symbols = new DecimalFormatSymbols();
        symbols.setCurrency(value);
        Runtime.getRuntime().exec(symbols.getNaN());
    }

    @GetMapping("/passthrough/decimal-format/codeDoesNotSetInfinity")
    public void codeDoesNotSetInfinity(@RequestParam String value) throws IOException {
        DecimalFormatSymbols symbols = new DecimalFormatSymbols();
        symbols.setInternationalCurrencySymbol(value);
        Runtime.getRuntime().exec(symbols.getInfinity());
    }

    @GetMapping("/passthrough/decimal-format/displaySymbolDoesNotSetCode")
    public void displaySymbolDoesNotSetCode(@RequestParam String value) throws IOException {
        DecimalFormatSymbols symbols = new DecimalFormatSymbols();
        symbols.setCurrencySymbol(value);
        Runtime.getRuntime().exec(symbols.getInternationalCurrencySymbol());
    }

}
