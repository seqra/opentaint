package rules;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.yaml.snakeyaml.Yaml;

/**
 * Locks down every semantic model-config change made since the field-sensitive
 * pass-through work began. A regression case is one normalized config action:
 * rule ordering and copy-action ordering are ignored, while access-path order,
 * field types, matchers, options, additions, removals, and duplicate counts are
 * significant.
 *
 * <p>The checked-in manifest is intentionally generated from Git objects. This
 * prevents a line-oriented YAML diff from mistaking moves for tests and makes a
 * newly edited config fail CI until its exact semantic delta is reviewed and
 * recorded.</p>
 */
public final class ModelConfigDiffCoverageCheck {
    private static final String BASE_COMMIT = "56a00bb32ebaa7b850b8ba41a4fe112d97200a92";
    private static final String MANIFEST = "rules/test/model-config-diff-coverage.tsv";
    private static final Pattern EXACT_SIGNATURE = Pattern.compile("^\\((.*)\\)\\s+(.+)$");
    private static final Pattern ARGUMENT = Pattern.compile("^arg\\((\\d+)\\)$");
    private static final Pattern FIELD = Pattern.compile("^\\.(.*)#([^#]+)#(.*)$");
    private static final Set<String> AGGREGATE_RESULTS = Set.of(
            "java.lang.String", "java.lang.Object", "byte", "char", "short", "int", "long",
            "float", "double", "boolean");
    private static final String SAMPLE =
            "security.passthrough.PassthroughValueFlowSamples#";
    private static final List<RegressionPair> REQUIRED_REGRESSION_PAIRS = List.of(
            pair("StringBuilder array elements", "stringBuilderAppendChars"),
            pair("byte-array output field", "byteArrayOutputStream"),
            pair("ByteBuffer storage", "byteBuffer"),
            pair("ByteBuffer destination", "byteBufferGet"),
            pair("CharBuffer storage", "charBuffer"),
            pair("CharBuffer destination", "charBufferGet"),
            pair("MessageFormat static pattern", "messageFormatStaticPattern"),
            pair("MessageFormat static arguments", "messageFormatStaticArgument"),
            pair("ChoiceFormat format array", "choiceFormatFormats"),
            pair("Jackson ObjectBuffer list elements", "objectBufferList"),
            pair("Jackson generator binary content", "jsonGeneratorBinary"),
            pair("List.replaceAll void result", "listReplaceAll"),
            pair("ConcurrentHashMap.replaceAll slots", "concurrentMapReplaceAll"),
            pair("FileSystem path varargs", "fileSystemPathVarargs"),
            pair("SearchControls attribute array", "searchControlsAttributes"),
            pair("BasicControl encoded payload", "basicControlPayload"),
            pair("Faces ArrayDataModel elements", "facesArrayDataModel"),
            pair("Faces SelectItemGroup elements", "facesSelectItemGroup"));
    private static final Set<String> REQUIRED_ISOLATION_REGRESSIONS = Set.of(
            SAMPLE + "messageFormatDoesNotFlowBackToArgumentsSafe",
            SAMPLE + "choiceFormatFormatsDoNotReachLimitsSafe",
            SAMPLE + "concurrentMapReplaceAllDoesNotMixKeysSafe",
            SAMPLE + "basicControlIdDoesNotReachPayloadSafe");

    private record Atom(String path, String section, String canonical, String description) {
        String fingerprint() {
            return sha256(path + "\0" + section + "\0" + canonical);
        }

    }

    private record Delta(char kind, Atom atom) {}

    private record RegressionPair(String issue, String positive, String negative) {}

    private ModelConfigDiffCoverageCheck() {}

    public static void main(String[] args) throws Exception {
        Path repository = Paths.get("../..").toRealPath();
        Path manifest = repository.resolve(MANIFEST);
        List<String> validationErrors = validateCurrentConfigs(repository);
        validateRegressionCoverage(repository, validationErrors);
        if (!validationErrors.isEmpty()) {
            System.err.println("Model config semantic validation failed:");
            validationErrors.forEach(error -> System.err.println("  " + error));
            System.exit(1);
        }
        List<Delta> actual = collectDeltas(repository);

        if (args.length == 1 && args[0].equals("--update")) {
            writeManifest(manifest, actual);
            System.out.println("Wrote " + actual.size() + " semantic config regression cases to " + manifest);
            return;
        }
        if (args.length != 0) {
            throw new IllegalArgumentException("usage: ModelConfigDiffCoverageCheck [--update]");
        }

        List<String> expected = Files.readAllLines(manifest, StandardCharsets.UTF_8);
        List<String> rendered = renderManifest(actual);
        if (!expected.equals(rendered)) {
            reportMismatch(expected, rendered);
            System.exit(1);
        }

        long additions = actual.stream().filter(delta -> delta.kind == '+').count();
        long removals = actual.size() - additions;
        System.out.println("Model config diff coverage passed: " + actual.size()
                + " exact semantic regression cases (" + additions + " additions, "
                + removals + " removals).");
    }

    private static RegressionPair pair(String issue, String stem) {
        return new RegressionPair(issue, SAMPLE + stem + "Unsafe", SAMPLE + stem + "Safe");
    }

    private static void validateRegressionCoverage(Path repository, List<String> errors)
            throws IOException {
        String registrations = Files.readString(repository.resolve("rules/test/rule-test.yaml"));
        for (RegressionPair pair : REQUIRED_REGRESSION_PAIRS) {
            if (!registrations.contains("- " + pair.positive)) {
                errors.add(pair.issue + " is missing positive regression " + pair.positive);
            }
            if (!registrations.contains("- " + pair.negative)) {
                errors.add(pair.issue + " is missing negative regression " + pair.negative);
            }
        }
        for (String regression : REQUIRED_ISOLATION_REGRESSIONS) {
            if (!registrations.contains("- " + regression)) {
                errors.add("field-isolation regression is missing: " + regression);
            }
        }
    }

    private static List<Delta> collectDeltas(Path repository) throws Exception {
        ensureBaseCommitExists(repository);
        List<String> changedPaths = command(repository, "git", "diff", "--name-only", BASE_COMMIT,
                "--", "model").lines().filter(line -> line.endsWith(".yaml")).sorted().toList();

        List<Delta> result = new ArrayList<>();
        for (String path : changedPaths) {
            List<Atom> before = atoms(path, gitFile(repository, BASE_COMMIT, path));
            Path currentFile = repository.resolve(path);
            List<Atom> after = Files.exists(currentFile)
                    ? atoms(path, Files.readAllBytes(currentFile))
                    : List.of();
            subtract(before, after, '-', result);
            subtract(after, before, '+', result);
        }
        result.sort(Comparator.comparing((Delta delta) -> delta.atom.path)
                .thenComparing(delta -> delta.atom.section)
                .thenComparing(delta -> delta.kind)
                .thenComparing(delta -> delta.atom.fingerprint())
                .thenComparing(delta -> delta.atom.canonical));
        return result;
    }

    private static List<String> validateCurrentConfigs(Path repository) throws Exception {
        List<String> errors = new ArrayList<>();
        List<String> changedPaths = command(repository, "git", "diff", "--name-only", BASE_COMMIT,
                "--", "model/java/config").lines().filter(line -> line.endsWith(".yaml")).sorted().toList();
        for (String path : changedPaths) {
            Path file = repository.resolve(path);
            if (!Files.exists(file)) {
                continue;
            }
            Object loaded;
            try (var input = Files.newInputStream(file)) {
                loaded = new Yaml().load(input);
            }
            Object rulesObject = loaded instanceof Map<?, ?> map ? map.get("passThrough") : loaded;
            if (!(rulesObject instanceof List<?> rules)) {
                continue;
            }
            for (int index = 0; index < rules.size(); index++) {
                if (rules.get(index) instanceof Map<?, ?> rule) {
                    validateRule(path, index, rule, errors);
                }
            }
        }
        validateFieldIdentities(repository.resolve("model"), errors);
        return errors;
    }

    private static void validateRule(String path, int index, Map<?, ?> rule, List<String> errors) {
        Object signatureObject = rule.get("signature");
        List<String> parameters = List.of();
        String returnType = "*";
        boolean exactParameters = false;
        if (signatureObject instanceof String signature) {
            Matcher signatureMatcher = EXACT_SIGNATURE.matcher(signature);
            if (signatureMatcher.matches()) {
                parameters = splitParameters(signatureMatcher.group(1));
                returnType = signatureMatcher.group(2);
                exactParameters = true;
            }
        } else if (signatureObject instanceof Map<?, ?> signature) {
            if (signature.get("return") != null) {
                returnType = String.valueOf(signature.get("return"));
            }
            parameters = matcherParameterTypes(signature.get("params"));
        }
        Object copiesObject = rule.get("copy");
        if (!(copiesObject instanceof List<?> copies)) {
            return;
        }
        String function = String.valueOf(rule.get("function"));
        String location = path + ":passThrough[" + index + "] " + function;
        for (Object copyObject : copies) {
            if (!(copyObject instanceof Map<?, ?> copy)) {
                continue;
            }
            validateEndpoint(location, "from", copy.get("from"), parameters, exactParameters,
                    returnType, errors);
            validateEndpoint(location, "to", copy.get("to"), parameters, exactParameters,
                    returnType, errors);
            validateElementCollapse(location, function, copy.get("from"), copy.get("to"),
                    parameters, returnType, errors);
            if (exactParameters) {
                validateFieldCollapse(location, function, copy.get("from"), copy.get("to"),
                        parameters, returnType, errors);
            }
        }
    }

    private static void validateEndpoint(String location, String side, Object endpoint,
            List<String> parameters, boolean exactParameters, String returnType, List<String> errors) {
        List<?> parts = endpoint instanceof List<?> list ? list : List.of(endpoint);
        if (parts.isEmpty()) {
            return;
        }
        String base = String.valueOf(parts.get(0));
        Matcher argument = ARGUMENT.matcher(base);
        if (exactParameters && argument.matches()
                && Integer.parseInt(argument.group(1)) >= parameters.size()) {
            errors.add(location + " has out-of-range " + side + " endpoint " + endpoint);
        }
        if (base.equals("result") && returnType.equals("void")) {
            errors.add(location + " uses " + side + "=result for a void method");
        }
        if (parts.size() > 1 && parts.get(1).equals("[*]")) {
            String baseType = endpointBaseType(base, parameters, returnType);
            if (baseType != null && !baseType.equals("*") && !baseType.endsWith("[]")) {
                errors.add(location + " applies [*] to non-array " + baseType + " at " + side);
            }
        }
        for (int i = 0; i + 1 < parts.size(); i++) {
            Matcher field = FIELD.matcher(String.valueOf(parts.get(i)));
            if (field.matches() && parts.get(i + 1).equals("[*]")) {
                String fieldType = field.group(3);
                if (!fieldType.endsWith("[]") && !fieldType.equals("java.lang.Object")) {
                    errors.add(location + " applies [*] after non-array field " + parts.get(i));
                }
            }
        }
    }

    private static void validateElementCollapse(String location, String function, Object from, Object to,
            List<String> parameters, String returnType, List<String> errors) {
        if (!(from instanceof List<?> fromParts) || fromParts.isEmpty()
                || !fromParts.get(fromParts.size() - 1).equals("[*]") || to instanceof List<?>) {
            return;
        }
        String target = String.valueOf(to);
        boolean stringConstruction = function.equals("java.lang.String#<init>");
        if (!stringConstruction && (target.equals("this") || ARGUMENT.matcher(target).matches())) {
            errors.add(location + " collapses an array element into whole " + target);
        }
        if (target.equals("result") && !returnType.endsWith("[]")
                && !AGGREGATE_RESULTS.contains(returnType) && !returnType.equals("*")) {
            errors.add(location + " collapses an array element into whole result of type " + returnType);
        }
    }

    private static void validateFieldCollapse(String location, String function, Object from, Object to,
            List<String> parameters, String returnType, List<String> errors) {
        if (!(from instanceof List<?> fromParts) || fromParts.size() < 2 || to instanceof List<?>) {
            return;
        }
        Matcher field = FIELD.matcher(String.valueOf(fromParts.get(fromParts.size() - 1)));
        if (!field.matches()) {
            return;
        }
        String target = String.valueOf(to);
        String fieldType = field.group(3);
        String targetType = endpointBaseType(target, parameters, returnType);
        boolean compatibleArrays = targetType != null && targetType.endsWith("[]")
                && fieldType.endsWith("[]");
        boolean compatible = targetType != null && (targetType.equals(fieldType)
                || fieldType.equals("java.lang.Object") || compatibleArrays);
        if ((target.equals("this") || ARGUMENT.matcher(target).matches()) && !compatible) {
            errors.add(location + "widens field " + field.group() + " into whole " + target);
            return;
        }
        String owner = function.contains("#") ? function.substring(0, function.indexOf('#')) : "";
        boolean fluentResult = returnType.equals(owner);
        if (!target.equals("result") || returnType.equals("*") || compatible
                || AGGREGATE_RESULTS.contains(returnType) || !fluentResult) {
            return;
        }
        errors.add(location + "widens field " + field.group() + " into incompatible whole result "
                + returnType);
    }

    private static String endpointBaseType(String base, List<String> parameters, String returnType) {
        Matcher argument = ARGUMENT.matcher(base);
        if (argument.matches()) {
            int index = Integer.parseInt(argument.group(1));
            return index < parameters.size() ? parameters.get(index) : null;
        }
        return base.equals("result") ? returnType : null;
    }

    private static List<String> splitParameters(String parameters) {
        if (parameters.isBlank()) {
            return List.of();
        }
        List<String> result = new ArrayList<>();
        for (String parameter : parameters.split(",")) {
            result.add(parameter.strip());
        }
        return result;
    }

    private static List<String> matcherParameterTypes(Object paramsObject) {
        if (!(paramsObject instanceof List<?> params)) {
            return List.of();
        }
        int maximum = -1;
        for (Object value : params) {
            if (value instanceof Map<?, ?> param && param.get("index") instanceof Number index) {
                maximum = Math.max(maximum, index.intValue());
            }
        }
        if (maximum < 0) {
            return List.of();
        }
        List<String> result = new ArrayList<>();
        for (int index = 0; index <= maximum; index++) {
            result.add("*");
        }
        for (Object value : params) {
            if (value instanceof Map<?, ?> param && param.get("index") instanceof Number index
                    && param.get("type") != null) {
                result.set(index.intValue(), String.valueOf(param.get("type")));
            }
        }
        return result;
    }

    private static void validateFieldIdentities(Path modelRoot, List<String> errors) throws IOException {
        Map<String, Map<String, List<String>>> identities = new TreeMap<>();
        try (var paths = Files.walk(modelRoot)) {
            for (Path path : paths.filter(file -> file.toString().endsWith(".yaml")).toList()) {
                Object loaded;
                try (var input = Files.newInputStream(path)) {
                    loaded = new Yaml().load(input);
                }
                collectFields(loaded, modelRoot.relativize(path).toString(), identities);
            }
        }
        identities.forEach((identity, types) -> {
            if (types.size() > 1) {
                errors.add("field " + identity + " has conflicting declared types " + types.keySet());
            }
        });
    }

    private static void collectFields(Object value, String path,
            Map<String, Map<String, List<String>>> identities) {
        if (value instanceof Map<?, ?> map) {
            map.values().forEach(item -> collectFields(item, path, identities));
        } else if (value instanceof List<?> list) {
            list.forEach(item -> collectFields(item, path, identities));
        } else if (value instanceof String string) {
            Matcher field = FIELD.matcher(string);
            if (field.matches()) {
                String identity = field.group(1) + "#" + field.group(2);
                identities.computeIfAbsent(identity, ignored -> new TreeMap<>())
                        .computeIfAbsent(field.group(3), ignored -> new ArrayList<>()).add(path);
            }
        }
    }

    private static void subtract(List<Atom> left, List<Atom> right, char kind, List<Delta> output) {
        Map<String, Integer> remaining = new HashMap<>();
        for (Atom atom : right) {
            remaining.merge(atom.section + "\0" + atom.canonical, 1, Integer::sum);
        }
        for (Atom atom : left) {
            String key = atom.section + "\0" + atom.canonical;
            int count = remaining.getOrDefault(key, 0);
            if (count == 0) {
                output.add(new Delta(kind, atom));
            } else {
                remaining.put(key, count - 1);
            }
        }
    }

    private static List<Atom> atoms(String path, byte[] yamlBytes) {
        if (yamlBytes == null) {
            return List.of();
        }
        Object loaded = new Yaml().load(new ByteArrayInputStream(yamlBytes));
        List<Atom> atoms = new ArrayList<>();
        if (loaded instanceof List<?> rootRules) {
            for (Object rule : rootRules) {
                addRuleAtoms(atoms, path, "<root>", rule);
            }
            return atoms;
        }
        if (!(loaded instanceof Map<?, ?> root)) {
            throw new IllegalStateException("Config root is neither a map nor a list: " + path);
        }
        for (Map.Entry<?, ?> rootEntry : root.entrySet()) {
            String section = String.valueOf(rootEntry.getKey());
            Object value = rootEntry.getValue();
            if (value instanceof List<?> rules) {
                for (Object rule : rules) {
                    addRuleAtoms(atoms, path, section, rule);
                }
            } else {
                atoms.add(new Atom(path, section, canonical(value), display(value)));
            }
        }
        return atoms;
    }

    private static void addRuleAtoms(List<Atom> atoms, String path, String section, Object rule) {
        if (!(rule instanceof Map<?, ?> ruleMap) || !(ruleMap.get("copy") instanceof List<?> copies)) {
            atoms.add(new Atom(path, section, canonical(rule), display(rule)));
            return;
        }

        Map<Object, Object> context = new LinkedHashMap<>();
        for (Map.Entry<?, ?> entry : ruleMap.entrySet()) {
            if (!String.valueOf(entry.getKey()).equals("copy")) {
                context.put(entry.getKey(), entry.getValue());
            }
        }
        String contextCanonical = canonical(context);
        for (Object copy : copies) {
            String canonical = "context=" + contextCanonical + ";copy=" + canonical(copy);
            atoms.add(new Atom(path, section, canonical,
                    "rule=" + display(context) + "; copy=" + display(copy)));
        }
        if (copies.isEmpty()) {
            atoms.add(new Atom(path, section, "context=" + contextCanonical + ";copy=[]",
                    "rule=" + display(context) + "; copy=[]"));
        }
    }

    private static String canonical(Object value) {
        if (value == null) {
            return "null";
        }
        if (value instanceof Map<?, ?> map) {
            List<Map.Entry<?, ?>> entries = new ArrayList<>(map.entrySet());
            entries.sort(Comparator.comparing(entry -> String.valueOf(entry.getKey())));
            StringBuilder result = new StringBuilder("{");
            for (Map.Entry<?, ?> entry : entries) {
                appendSized(result, String.valueOf(entry.getKey()));
                result.append('=');
                appendSized(result, canonical(entry.getValue()));
            }
            return result.append('}').toString();
        }
        if (value instanceof List<?> list) {
            StringBuilder result = new StringBuilder("[");
            for (Object item : list) {
                appendSized(result, canonical(item));
            }
            return result.append(']').toString();
        }
        String type = value instanceof String ? "s" : value instanceof Boolean ? "b" : "n";
        return type + value;
    }

    private static void appendSized(StringBuilder output, String value) {
        output.append(value.length()).append(':').append(value);
    }

    private static byte[] gitFile(Path repository, String revision, String path) throws Exception {
        Process process = new ProcessBuilder("git", "show", revision + ":" + path)
                .directory(repository.toFile()).start();
        ByteArrayOutputStream stdout = new ByteArrayOutputStream();
        ByteArrayOutputStream stderr = new ByteArrayOutputStream();
        process.getInputStream().transferTo(stdout);
        process.getErrorStream().transferTo(stderr);
        int exit = process.waitFor();
        if (exit == 0) {
            return stdout.toByteArray();
        }
        String error = stderr.toString(StandardCharsets.UTF_8);
        if (error.contains("exists on disk, but not in") || error.contains("does not exist in")) {
            return null;
        }
        throw new IllegalStateException("git show failed for " + path + ": " + error.strip());
    }

    private static void ensureBaseCommitExists(Path repository) throws Exception {
        Process process = new ProcessBuilder("git", "cat-file", "-e", BASE_COMMIT + "^{commit}")
                .directory(repository.toFile()).inheritIO().start();
        if (process.waitFor() != 0) {
            throw new IllegalStateException("Required config-regression base commit is unavailable: "
                    + BASE_COMMIT + ". CI checkouts must use fetch-depth: 0.");
        }
    }

    private static String command(Path directory, String... command) throws Exception {
        Process process = new ProcessBuilder(command).directory(directory.toFile()).start();
        String stdout = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
        String stderr = new String(process.getErrorStream().readAllBytes(), StandardCharsets.UTF_8);
        int exit = process.waitFor();
        if (exit != 0) {
            throw new IllegalStateException(String.join(" ", command) + " failed: " + stderr.strip());
        }
        return stdout;
    }

    private static List<String> renderManifest(List<Delta> deltas) {
        List<String> lines = new ArrayList<>();
        lines.add("# Exact semantic regression coverage for model config changes.");
        lines.add("# Generated by: ./gradlew checkModelConfigDiffCoverage --args=--update");
        lines.add("base\t" + BASE_COMMIT);
        for (Delta delta : deltas) {
            lines.add(delta.kind + "\t" + delta.atom.path + "\t" + delta.atom.section + "\t"
                    + delta.atom.fingerprint() + "\t" + delta.atom.description());
        }
        return lines;
    }

    private static void writeManifest(Path manifest, List<Delta> deltas) throws IOException {
        Files.write(manifest, renderManifest(deltas), StandardCharsets.UTF_8);
    }

    private static void reportMismatch(List<String> expected, List<String> actual) {
        Map<String, Integer> expectedCounts = counts(expected);
        Map<String, Integer> actualCounts = counts(actual);
        List<String> missing = countDifference(expectedCounts, actualCounts);
        List<String> unexpected = countDifference(actualCounts, expectedCounts);
        System.err.println("Model config diff coverage failed. Every semantic config change must have an exact regression case.");
        printExamples("Missing/stale manifest cases", missing);
        printExamples("Uncovered semantic changes", unexpected);
        System.err.println("After reviewing every reported action, regenerate with:");
        System.err.println("  ./gradlew checkModelConfigDiffCoverage --args=--update");
    }

    private static Map<String, Integer> counts(List<String> lines) {
        Map<String, Integer> result = new TreeMap<>();
        lines.forEach(line -> result.merge(line, 1, Integer::sum));
        return result;
    }

    private static List<String> countDifference(Map<String, Integer> left, Map<String, Integer> right) {
        List<String> result = new ArrayList<>();
        left.forEach((line, count) -> {
            int difference = count - right.getOrDefault(line, 0);
            if (difference > 0) {
                result.add(difference == 1 ? line : line + " (" + difference + " occurrences)");
            }
        });
        return result;
    }

    private static void printExamples(String title, List<String> lines) {
        if (lines.isEmpty()) {
            return;
        }
        System.err.println(title + " (" + lines.size() + "):");
        lines.stream().limit(25).forEach(line -> System.err.println("  " + line));
        if (lines.size() > 25) {
            System.err.println("  ... and " + (lines.size() - 25) + " more");
        }
    }

    private static String display(Object value) {
        String rendered;
        if (value instanceof Map<?, ?> map) {
            List<String> entries = new ArrayList<>();
            for (Map.Entry<?, ?> entry : map.entrySet()) {
                entries.add(entry.getKey() + "=" + display(entry.getValue()));
            }
            entries.sort(String::compareTo);
            rendered = "{" + String.join(", ", entries) + "}";
        } else if (value instanceof List<?> list) {
            rendered = "[" + list.stream().map(ModelConfigDiffCoverageCheck::display)
                    .reduce((left, right) -> left + ", " + right).orElse("") + "]";
        } else {
            rendered = String.valueOf(value);
        }
        rendered = rendered.replace("\t", " ").replace("\n", " ").replace("\r", " ");
        return rendered.length() <= 300 ? rendered : rendered.substring(0, 297) + "...";
    }

    private static String sha256(String value) {
        try {
            byte[] digest = MessageDigest.getInstance("SHA-256")
                    .digest(value.getBytes(StandardCharsets.UTF_8));
            return java.util.HexFormat.of().formatHex(digest);
        } catch (NoSuchAlgorithmException e) {
            throw new AssertionError(e);
        }
    }
}
