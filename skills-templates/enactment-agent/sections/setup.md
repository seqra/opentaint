Skip only what `appsec-agent` already did when it handed off — the toolchain and nesting checks. Everything from step 3 on is this pipeline's own, including the bootstrap.

### 1. Confirm the toolchain

Confirm `opentaint` is on PATH with `opentaint -v`. If it's missing, don't proceed silently — tell the user and offer the install command for their platform, run an install only on explicit confirmation:

- macOS / Linux, in order: `brew install --cask seqra/tap/opentaint` · `npm install -g @seqra/opentaint`
- Windows: `npm install -g @seqra/opentaint`

After installing, run `opentaint health` to confirm everything's resolved.

### 2. Confirm agent nesting

This workflow requires two subagent levels: MAIN → stage orchestrator → leaf. Confirm the harness permits depth 2 before starting; otherwise ask the user to enable it.

### 3. Locate the findings

The supplied findings are this run's input and the only thing it is measured against. Ask the user for their path when it isn't already given — a manifest, SARIF, scanner report, or a directory of finding documents. If the user has only described the findings in conversation, write them to a file first and use that; the pipeline resumes from disk, not from this thread.

### 4. Determine the language

Read the project's build files to fix the target language — Maven/Gradle → java, `go.mod` → go, and so on. Record it at bootstrap; stage orchestrators pass it to language-coupled leaves.

### 5. Choose the workflow

Ask the user for both knobs together:

1. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — static + PoC per confirmed TP. This launches a few test services on the user's machine (local instances and ports), torn down at the end of the run. Make that clear in the option
2. Controls — `on` · `off`, the precision pass that lands sanitizers, negative patterns, and context restrictions before the run closes
   - on (recommended) — the boundaries' own controls land, triage's false positives get restricted, and the reproduction is measured against rules that are precise enough to keep
   - off — coverage is measured on the raw boundaries. Reproduction still counts by trace identity, so a finding overmatched by a wide rule still counts as reproduced; the rules just stay unrestricted. Offer this when the user only wants to know what is reachable

There is no scan-level question here: reproducing a finding set always needs the full rule and approximation toolbox, so enactment is always deep.

### 6. Bootstrap

Seed the run state and the working tree:

```bash
uv run <skill-dir>/scripts/generate.py init --mode enactment --triage-level <static|dynamic> --controls <on|off> --language <lang> --findings <path>
```

It writes `state.yaml`, seeds `history.yaml`, and creates the `.opentaint/` tree including `tracking/reference/` and `tracking/boundaries/`. It refuses to convert an existing assessment run — that tracking has no reference set behind it, so enactment starts in its own project tree.
