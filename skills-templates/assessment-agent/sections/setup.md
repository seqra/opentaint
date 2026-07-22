Skip only what `appsec-agent` already did when it handed off — the toolchain and nesting checks. Everything from step 3 on is this pipeline's own, including the bootstrap.

### 1. Confirm the toolchain

Confirm `opentaint` is on PATH with `opentaint -v`. If it's missing, don't proceed silently — tell the user and offer the install command for their platform, run an install only on explicit confirmation:

- macOS / Linux, in order: `brew install --cask seqra/tap/opentaint` · `npm install -g @seqra/opentaint`
- Windows: `npm install -g @seqra/opentaint`

After installing, run `opentaint health` to confirm everything's resolved.

### 2. Confirm agent nesting

This workflow requires two subagent levels: MAIN → stage orchestrator → leaf. Confirm the harness permits depth 2 before starting; otherwise ask the user to enable it.

### 3. Determine the language

Read the project's build files to fix the target language — Maven/Gradle → java, `go.mod` → go, and so on. Record it at bootstrap; stage orchestrators pass it to language-coupled leaves. When a repo carries build markers for more than one, ask the user which to analyze.

For `go`, also confirm `go` is on PATH (`command -v go`) before bootstrapping — the analyzer drives the Go toolchain at both build and scan time, so a Go run hard-fails without it. Tell the user and stop if it's missing. Two pipeline branches are Java-only and simply don't run for Go: dataflow approximations (Go has only passThrough) and everything that depends on them.

### 4. Choose the workflow

Ask the user for all three knobs together:

1. Scan level — `lite` · `normal` · `deep`
   - lite — build + scan (expected, when there are already existing artifacts)
   - normal — build + scan + custom approximations
   - deep — build + scan + custom approximations + custom rules
   - recommend by what's on disk: a cold start (no `.opentaint` artifacts) → deep; a prior run's artifacts already present → lite
2. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — static + PoC per confirmed TP. This launches a few test services on the user's machine (local instances and ports), torn down at the end of the run. Make that clear in the option
3. Controls — `on` · `off`, the precision pass that lands sanitizers, negative patterns, and context restrictions on the created rules after triage
   - on (recommended) — false positives triage found get restricted, and the created rules stay reusable for later runs
   - off — the report keeps every candidate result as triaged, and the created rules stay as first authored. Offer this when the user wants maximum recall or is done after the report
   - only asked for a `deep` run; lite and normal author no rules to restrict

### 5. Bootstrap

Seed the run state and the working tree with the chosen levels and language:

```bash
uv run <skill-dir>/scripts/generate.py init --scan-level <lite|normal|deep> --triage-level <static|dynamic> --controls <on|off> --language <lang>
```

It writes `state.yaml` with `mode: assessment`, seeds `history.yaml`, and creates the `.opentaint/` tree.
