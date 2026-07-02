package rules;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.yaml.snakeyaml.Yaml;

/**
 * CI helper that checks that:
 * 1) every YAML in ../ruleset is valid;
 * 2) every non-disabled and non-lib rule is covered by a rule-test.yaml entry.
 *
 * Fails with non-zero exit code and prints all problems.
 */
public class RuleCoverageCheck {

    private record RuleKey(String rulePath, String id) {}

    public static void main(String[] args) throws Exception {
        Path projectRoot = Paths.get("..").toRealPath();
        Path rulesRoot = projectRoot.resolve("ruleset");
        Path testsRoot = projectRoot.resolve("test");

        List<String> errors = new ArrayList<>();

        if (!Files.isDirectory(rulesRoot)) {
            errors.add("Rules directory not found: " + rulesRoot);
        }
        if (!Files.isDirectory(testsRoot)) {
            errors.add("Tests directory not found: " + testsRoot);
        }

        if (!errors.isEmpty()) {
            printErrorsAndExit(errors);
        }

        Map<RuleKey, Path> activeRules = collectActiveRules(rulesRoot, errors, rulesRoot);
        Set<RuleKey> coveredRules = collectCoveredRules(testsRoot);

        for (RuleKey rule : activeRules.keySet()) {
            if (!coveredRules.contains(rule)) {
                errors.add("UNCOVERED RULE: path='" + rule.rulePath + "', id='" + rule.id + "'");
            }
        }

        if (!errors.isEmpty()) {
            printErrorsAndExit(errors);
        }

        System.out.println("Rule coverage check passed: all rules valid and covered.");
    }

    private static Map<RuleKey, Path> collectActiveRules(Path rulesRoot, List<String> errors, Path projectRoot) throws IOException {
        Map<RuleKey, Path> result = new LinkedHashMap<>();
        Yaml yaml = new Yaml();

        Files.walkFileTree(rulesRoot, new SimpleFileVisitor<>() {
            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
            if (!file.getFileName().toString().endsWith(".yaml")) {
                return FileVisitResult.CONTINUE;
            }

            String relativeRulePath = projectRoot.relativize(file.toAbsolutePath()).toString().replace('\\', '/');
            try (InputStream in = Files.newInputStream(file)) {
                Object loaded = yaml.load(in);
                if (!(loaded instanceof Map<?, ?> map)) {
                    errors.add("INVALID YAML (root not a map): " + relativeRulePath);
                    return FileVisitResult.CONTINUE;
                }
                Object rulesObj = map.get("rules");
                if (!(rulesObj instanceof Iterable<?> iterable)) {
                    errors.add("INVALID YAML (missing 'rules' list): " + relativeRulePath);
                    return FileVisitResult.CONTINUE;
                }

                for (Object ruleObj : iterable) {
                    if (!(ruleObj instanceof Map<?, ?> ruleMap)) {
                        errors.add("INVALID RULE ENTRY (not a map) in " + relativeRulePath);
                        continue;
                    }
                    Object idObj = ruleMap.get("id");
                    if (!(idObj instanceof String id) || id.isBlank()) {
                        errors.add("INVALID RULE ENTRY (missing/blank id) in " + relativeRulePath);
                        continue;
                    }

                    boolean disabled = false;
                    boolean lib = false;
                    Object optionsObj = ruleMap.get("options");
                    if (optionsObj instanceof Map<?, ?> options) {
                        Object disabledObj = options.get("disabled");
                        if (disabledObj instanceof String) {
                            disabled = true;
                        }
                        Object libObj = options.get("lib");
                        if (libObj instanceof Boolean b) {
                            lib = b;
                        }
                    }

                    if (!disabled && !lib) {
                        result.put(new RuleKey(relativeRulePath, id), file);
                    }
                }
            } catch (Exception e) {
                errors.add("INVALID YAML (parse error): " + relativeRulePath + " - " + e.getMessage());
            }

            return FileVisitResult.CONTINUE;
            }
        });

        return result;
    }

    private static Set<RuleKey> collectCoveredRules(Path testsRoot) throws IOException {
        Set<RuleKey> covered = new HashSet<>();
        Yaml yaml = new Yaml();

        Files.walkFileTree(testsRoot, new SimpleFileVisitor<>() {
            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
            if (!file.getFileName().toString().equals("rule-test.yaml")) {
                return FileVisitResult.CONTINUE;
            }

            try (InputStream in = Files.newInputStream(file)) {
                Object loaded = yaml.load(in);
                if (!(loaded instanceof Map<?, ?> map)) {
                    return FileVisitResult.CONTINUE;
                }
                Object testsObj = map.get("tests");
                if (!(testsObj instanceof Iterable<?> tests)) {
                    return FileVisitResult.CONTINUE;
                }
                for (Object testObj : tests) {
                    if (!(testObj instanceof Map<?, ?> testMap)) {
                        continue;
                    }
                    Object ruleIdObj = testMap.get("rule-id");
                    if (!(ruleIdObj instanceof String ruleId)) {
                        continue;
                    }
                    int separator = ruleId.indexOf('#');
                    if (separator <= 0 || separator == ruleId.length() - 1) {
                        continue;
                    }
                    String rulePath = ruleId.substring(0, separator).replace('\\', '/');
                    String id = ruleId.substring(separator + 1);
                    covered.add(new RuleKey(rulePath, id));
                }
            }

            return FileVisitResult.CONTINUE;
            }
        });

        return covered;
    }

    private static void printErrorsAndExit(List<String> errors) {
        System.err.println("Rule coverage check failed with " + errors.size() + " problem(s):");
        for (String e : errors) {
            System.err.println(" - " + e);
        }
        System.exit(1);
    }
}
