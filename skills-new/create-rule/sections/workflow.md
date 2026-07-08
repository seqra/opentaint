### 1. Check existing coverage

Browse the built-in library rules for a source or sink you can reference — a `refs` to a built-in is cheaper and more accurate than authoring a completely new rule. For listing available rules run

```bash
opentaint health --rules
```

In fix mode, don't author from the unit: go straight to that one flagged rule, adjust it by the false-positive/negative guidance per step 4, re-run this side's tests, and stop — leave the unit's other entries untouched. Otherwise, when the unit's rules already exist and pass (entries carry `rule_id` and `stages.tests_passing: done`), reuse them as the baseline and extend only for what the unit newly names. When the unit is partway (some stages `done`, some not), continue from the first unfinished stage on the artifacts already on disk rather than restarting, authoring from scratch only the genuinely new sources or sinks.

### 2. Author the library rules

Derive each rule's pattern from the unit's fully-qualified names, recorded signatures, and annotations. Bind the tainted value to one consistent metavariable in every rule so the security joins assembled later reference one name. The rule forms — a built-in `refs`, a custom source rule, a custom sink rule, and where custom rules go — are in the language reference.

### 3. Write the test joins

A library rule emits nothing on its own — to exercise it, wire it to the generic taint marker in a throwaway test join. Write one join for the side into the test project's marker rules, referencing the generic marker on one end and each new lib rule on the other, so a positive sample's tainted value flows marker-to-rule (a sink side) or rule-to-marker (a source side). These joins live only in the test project, never in the scanned rules tree, so the main scan never loads them. The join form, its naming, and where it goes are in the language reference.

### 4. Test until success

Run the rule tests over the compiled sub-model, loading your lib rules and the test joins + markers, and iterate until every sample passes:

```bash
opentaint test rule run .opentaint/test-compiled/<unit>/<side> \
  -o .opentaint/test-results/<unit>/<side> \
  --ruleset .opentaint/rules --ruleset .opentaint/test-projects/<unit>/<side>/test-rules \
  --passthrough-approximations .opentaint/pass-through \
  --dataflow-approximations .opentaint/dataflow
```

`test rule run` auto-loads the built-in rules, so pass only your custom rulesets. Apply the approximation directories as-is, an empty one is harmless. Read `.opentaint/test-results/<unit>/<side>/test-result.json` and fix by the verdict:

- `falseNegative` → the match is too narrow, broaden it and confirm the metavariable names line up across branches and between `refs` and `on`
- `falsePositive` → the match is too broad, add an exclusion or a sanitizer
- `skipped` / `disabled` → the rule wasn't exercised; fix the sample's annotation target, or enable the rule

The concrete pattern operators for each fix are in the language reference.

### 5. Escalate when a positive won't converge

A positive that won't pass after ~3 rule fixes may have a cause no rule edit can fix. Localize the cause per `references/debugging.md`, then leave `stages.tests_passing: pending` and report it (per Output), rather than editing blindly.
