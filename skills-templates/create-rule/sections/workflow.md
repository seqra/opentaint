### 1. Check existing coverage

Browse the built-in library rules and `.opentaint/rules` to determine whether one already matches each unit entry. When one does, do not author a duplicate: set its `rule_id` in `.opentaint/tracking/rules/<side>/<unit>.yaml` to `<relative-yaml-path>#<rule-id>`. This string is tracking bookkeeping only. Do not add a `rule` reference to any production rule, production joins remain tag-based and are written later. The following command prints the built-in rules root path. Browse both roots using the language reference and search by the entry's exact language-specific identifier:

```bash
opentaint health --rules
```

Read `.opentaint/tracking/rules/tags.yaml`. A source unit must carry `tag: untrusted-data-source`, each sink unit group carries the one existing or newly registered `*-sink` tag its rules must extend.

In fix mode, don't author from the unit: go straight to that one flagged rule, adjust it by the false-positive/negative guidance per step 4, re-run this side's tests, and stop — leave the unit's other entries untouched. Otherwise, when entries already carry `rule_id`, continue from those recorded implementations and author only entries still lacking coverage. When the unit is partway (some stages `done`, some not), continue from the first unfinished stage on the artifacts already on disk rather than restarting.

### 2. Author the library rules

Derive each rule's pattern from the unit's exact member identifiers, recorded signatures, and relevant declaration metadata. Bind the tainted value to `$UNTRUSTED` and put the unit/group tag on the lib rule. A sink tag belongs to the whole semantic group, not to an individual method. One rule can cover several group methods and several rules can carry the same tag. The rule forms and locations are in the language reference.

For `side: sinks`, iterate `groups`: ensure every method under `groups[].sinks` has an implementing `rule_id`, and put the enclosing `groups[].tag` on every custom rule you create. For `side: sources`, use the unit's top-level tag.

### 3. Write the test joins

A library rule emits nothing on its own — to exercise it, wire it to the generic taint marker in a throwaway test join. Write one join for the side into the test project's marker rules, referencing the generic marker on one end and each lib `rule_id` selected for the unit on the other, so a positive sample's tainted value flows marker-to-rule (a sink side) or rule-to-marker (a source side). The test joins live only in the test project, never in the scanned rules tree. Their form, naming, and location are in the language reference.

### 4. Test until success

Run the rule tests directly as a foreground, blocking command and wait for exit — never background them or use Monitor. Load your lib rules and the test joins + markers, and iterate until every sample passes:

```bash
opentaint test rule run .opentaint/test-compiled/<unit>/<side> \
  -o .opentaint/test-results/<unit>/<side> \
  --ruleset .opentaint/rules --ruleset .opentaint/test-projects/<unit>/<side>/test-rules \
  --passthrough-approximations .opentaint/pass-through
```

`test rule run` auto-loads the built-in rules, so pass only your custom rulesets. Apply the passthrough approximations as-is, an empty one is harmless. Read the result with the bundled script — it prints the pass/fail counts and names the failing samples, so you never parse the JSON by hand:

```bash
uv run <skill-dir>/scripts/check-test-result.py <unit>/<side>
```

Fix by the verdict it reports:

- `falseNegative` → the match is too narrow, broaden it and confirm the metavariable names line up across branches and between `refs` and `on`
- `falsePositive` → the match is too broad, add an exclusion or a sanitizer
- `skipped` / `disabled` → the rule wasn't exercised; fix the sample's `rule-test.yaml` entrypoint or `rule-id`, or enable the rule

The concrete pattern operators for each fix are in the language reference.

### 5. Escalate when a positive won't converge

A positive that won't pass after ~3 rule fixes may have a cause no rule edit can fix. Localize the cause per `references/debugging.md`, then leave `stages.tests_passing: pending` and report it (per Output), rather than editing blindly.
