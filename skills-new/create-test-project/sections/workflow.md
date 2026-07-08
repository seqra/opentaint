### 1. Scaffold the project

The scaffold command and sample form are language-specific — read the reference for your `type`: `references/<lang>-rule.md` for `rule-source` / `rule-sink`, or `references/<lang>-approximation.md` for `dataflow` (one self-contained reference, no need to read the other). Scaffold the project for the `type`, passing each of the unit's `dependencies` at its pinned version. The scaffold provides the generic taint marker and the fixed test rule the samples annotate against, so you author only the samples. If the `<name>` project already exists — re-invoked because its surface grew or a dependency moved — extend it instead: add the missing samples and recompile rather than scaffolding fresh. The init command is in that reference.

### 2. Write the samples

For each method to exercise, the unit or batch entry already records its `signature`; shape a faithful sample from how the method is really called in the project, then write minimal annotated samples. The app's real path is irrelevant, only that data flows between the method and the marker:

- the counterpart is always the generic marker, never a real source/sink, so the sample exercises only the unit under test
- annotate each sample with the single verdict it must produce — a positive that must flag, and, where the type calls for it, a negative that must not

The sample code, its annotations, and which verdicts a type needs are in that reference.

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
