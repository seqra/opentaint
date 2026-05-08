---
name: opentaint-issue-investigation
description: Build a minimal reproducer and pinpoint the instruction where OpenTaint's engine drops a dataflow fact, then write a short engine-issue report. Use as a last resort when a rule passes its tests, the library model is complete, and the finding is still wrong.
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.1"
---

# Skill: OpenTaint Issue Investigation

Investigate and confirm an issue in the OpenTaint analysis engine — a case where a rule that should fire does not (or fires where it should not), and the cause is **not** the rule's syntax or the library modeling, but the engine itself (e.g. an intra/inter-procedural dataflow path that is cut unexpectedly).

The deliverable is a small, self-contained reproducer plus a short write-up that points at the exact instruction where the dataflow dies.

## When to use this skill

Use it after `analyze-findings` / `create-yaml-config` / `create-approximation` have been exhausted and a finding is still missing (or spurious), even though:

- The rule passes its own tests on isolated samples.
- `external-methods-without-rules.yaml` is empty (or irrelevant) for the relevant code path.
- Nothing about the library model is obviously wrong.

If any of those is not true, stop and go fix the rule / add the approximation first. An "engine issue" report is only credible once the trivial causes have been ruled out.

## Prerequisites

- Working rule with passing tests (`create-rule`, `test-rule`).
- Baseline scan has been run (`run-analysis`).
- `analyze-findings` has been consulted; the remaining failure is not explained by `external-methods-without-rules.yaml`.

## Procedure

### 1. Build a minimal rule-test reproducer

Shrink the original code to the smallest sample that still reproduces the problem, and put it in a rule-test project under `.opentaint/test-project/` at the analyzed project root (read the `test-rule` skill).

Choose the project shape based on what the real code needs:

- **Plain method-level sample** — works for rules where the tainted flow stays inside one method or crosses only ordinary Java calls. One class under `src/main/java/test/` with a single `@PositiveRuleSample` (expected trigger) or `@NegativeRuleSample` (expected no trigger) is enough.
- **Spring-app sub-project** — required whenever the real flow enters through a Spring `@Controller`, uses Spring beans, or depends on dispatcher wiring. Create a dedicated `spring-app-tests/<name>` module with exactly one sample annotation, as described in the `test-rule` skill under *Testing Spring-app rules*. Positive and negative cases go in separate sub-projects (e.g. `xss-spring-test-positive`, `xss-spring-test-negative`).

Keep the sample as small as possible: remove every statement that is not needed to carry taint from source to sink. A small reproducer is what makes the rest of the investigation tractable — and it is what ships in the bug report.

### 2. Confirm the issue reproduces on the test project

Compile the test project and run the rule tests:

```bash
opentaint compile .opentaint/test-project -o .opentaint/test-compiled
opentaint dev test-rules .opentaint/test-compiled \
  -o .opentaint/test-results \
  --ruleset builtin --ruleset .opentaint/rules
```

Inspect `.opentaint/test-results/test-result.json`:

- A `@PositiveRuleSample` that ends up in `falseNegative` reproduces a missed-detection engine issue.
- A `@NegativeRuleSample` that ends up in `falsePositive` reproduces a spurious-detection engine issue.
- `skipped` / `disabled` mean the rule was not actually exercised — fix the annotation `value`/`id` or enable the rule before going further.
- `success` means the issue does **not** reproduce. Either the sample is too reduced, or something in the original project (not in the sample) is what triggers the problem. Go back to step 1 and add back the minimum context.

Do not proceed until the test result matches the bug you are trying to document.

### 3. Rule out missed external-method models

Re-run the test with external-method tracking and read the two lists next to the SARIF (read the `analyze-findings` skill, §3):

```bash
opentaint scan --project-model .opentaint/test-compiled \
  -o .opentaint/test-results/report.sarif \
  --ruleset builtin --ruleset .opentaint/rules \
  --rule-id <ruleSetRelativePath>.yaml:<shortId> \
  --track-external-methods
```

Open `.opentaint/test-results/external-methods-without-rules.yaml`. For every method that sits on the source→sink path in your sample:

- Simple propagator (getter/collection/builder) → add a YAML `passThrough` (read the `create-yaml-config` skill).
- Lambda/callback/async → add a code-based approximation (read the `create-approximation` skill).

Re-run until that file contains **no methods on the relevant path**. Only then is it legitimate to call the remaining failure an engine issue — otherwise you are just looking at a missing library model.

### 4. Locate where the dataflow dies

Use the fact reachability debug command to see exactly how far the taint travels (read the `debug-rule-reachability` skill). It is a separate command, `opentaint dev debug-fact-reachability`, that takes a single full rule ID:

```bash
opentaint dev debug-fact-reachability \
  <ruleSetRelativePath>.yaml:<shortId> \
  --project-model .opentaint/test-compiled \
  -o .opentaint/test-results/report.sarif \
  --ruleset builtin --ruleset .opentaint/rules
```

Inspect `.opentaint/test-results/debug-ifds-fact-reachability.sarif`. For a missed detection:

1. Confirm the **source is matched** — at least one fact is reported at the source location. If it is not, the problem is in the rule's `pattern-sources`, not the engine.
2. Walk the reachable facts along the expected path. Note the **last instruction that still carries the fact** and the **first instruction where it is gone**. That gap is where the engine drops the dataflow.
3. Check that the drop happens at an instruction that is **not relevant to the rule** — e.g. a plain local assignment, a trivial method call with a modelled pass-through, a cast, a field read. If the drop is at something the rule should handle (a recognised sanitizer, a sink variant the rule was not written to match, etc.), the issue is still in the rule, not in the engine.

For a spurious detection, do the symmetric check: find the instruction where the fact appears even though no tainted input reaches it.

### 5. Write the investigation report

Produce a short Markdown note at `.opentaint/issues/<slug>.md` with:

- **Reproducer** — path to the rule-test sub-project, the exact `opentaint dev test-rules` command, and the relevant snippet from `test-result.json`.
- **Rule** — full rule ID (`<ruleSetRelativePath>.yaml:<shortId>`) and the ruleset it came from (`builtin` or `.opentaint/rules`).
- **Observed vs expected verdict** — e.g. *Expected: finding at `Sink.java:42`. Observed: no finding; sample listed under `falseNegative`.*
- **Where the dataflow dies** — file, line, and the specific instruction from the fact reachability SARIF. Quote the trace up to the last reachable fact and state which instruction drops it.
- **Ruled-out causes** —
  1. Rule tests pass on an isolated method sample (rule syntax is fine).
  2. `external-methods-without-rules.yaml` has no methods on the relevant path (library modeling is not the gap), or list the approximations that were added in step 3.
  3. The dropping instruction is unrelated to what the rule was meant to match (not a sanitizer, not an unsupported sink variant, etc.).
- **Minimal hypothesis** — 1–3 sentences on what the engine is likely doing wrong at that instruction (e.g. *"IFDS loses the fact across this `StringBuilder.append` because the call is devirtualized to an `AbstractStringBuilder` overload that has no default pass-through"*). Keep it short; this is a hypothesis, not a fix.

Include only what is needed to reproduce and locate the problem. A good report is roughly one screen of Markdown plus the rule-test sub-project.

## Stop Condition

The investigation is done when all of the following hold:

- The rule-test sub-project reproduces the issue deterministically via `opentaint dev test-rules`.
- No method on the expected source→sink path remains in `external-methods-without-rules.yaml`.
- The fact reachability SARIF pinpoints a specific instruction where the taint is dropped (or spuriously introduced) and that instruction is unrelated to the rule logic.
- The report at `.opentaint/issues/<slug>.md` exists and is self-contained.
