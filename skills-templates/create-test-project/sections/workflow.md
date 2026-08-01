### 1. Scaffold the project

The scaffold command and sample form are language-specific — read the reference for your `type`: `references/<lang>-rule.md` for `rule-source` / `rule-sink`, or `references/<lang>-approximation.md` for `dataflow` (one self-contained reference, no need to read the other). Scaffold the project for the `type`, passing each of the unit's `dependencies` at its pinned version. The scaffold provides the generic taint marker and fixed test rules, so you author only the samples. If the `<name>` project already exists — re-invoked because its surface grew or a dependency moved — extend it instead: add the missing samples and recompile rather than scaffolding fresh. The init command is in that reference.

### 2. Write the samples

For a unit or batch, each entry records its `signature`; shape a faithful sample from how that callable is really used in the project. The app's real path is irrelevant, only that data flows between the boundary and the marker:

For a sink unit, the methods are nested under `groups[].sinks`, exercise every method while preserving the group boundaries for the later rule author.

- the counterpart is always the generic marker, never a real source/sink, so the sample exercises only the unit under test
- for a rule side, register each sample under the single verdict it must produce
- for dataflow, register every sample under all four plain/starred source/sink rules, with exactly one deliberate positive or negative verdict per rule; never omit a scope combination

The sample code, the `rule-test.yaml` form, and which verdicts a type needs are in that reference.

### 3. Compile to the model

Compile the project you built to `.opentaint/test-compiled/<name>` — a rule side compiles the one sub-project you scaffolded (`sources/` or `sinks/`) to the matching sub-model, a dataflow project compiles once:

```bash
# rule side — the one you built
opentaint compile .opentaint/test-projects/<name>/sources -o .opentaint/test-compiled/<name>/sources
# dataflow
opentaint compile .opentaint/test-projects/<name> -o .opentaint/test-compiled/<name>
```

A clean compile is the deliverable. Feedback loop: a build failure is a fixable samples-or-dependencies problem — surface the real error, fix it, and recompile. On a clean compile set the test-project stage done (per Tracking).

### 4. Escalate

When a project won't compile after ~3 fixes with no clear cause → report the failure and leave the test-project stage pending, for the orchestrator to intervene.
