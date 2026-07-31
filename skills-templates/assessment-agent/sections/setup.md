Skip only what `appsec-agent` already did when it handed off — the toolchain and nesting checks. Everything from step 3 on is this pipeline's own, including the bootstrap.

### 1. Confirm the toolchain

Confirm `opentaint` is on PATH with `opentaint -v`. If it's missing, don't proceed silently — tell the user and offer the install command for their platform, run an install only on explicit confirmation:

- macOS / Linux, in order: `brew install --cask seqra/tap/opentaint` · `npm install -g @seqra/opentaint`
- Windows: `npm install -g @seqra/opentaint`

After installing, run `opentaint health` to confirm everything's resolved.

### 2. Confirm agent nesting

This workflow requires two subagent levels: MAIN → stage orchestrator → leaf. Confirm the harness permits depth 2 before starting; otherwise ask the user to enable it.

### 3. Determine the language

Read the project's build files to fix the target language — Maven/Gradle → java, `go.mod` → go, and so on. Record it at bootstrap; stage orchestrators pass it to language-coupled leaves.

### 4. Choose the workflow

Ask the user for both knobs together:

1. Scan level — `lite` · `normal` · `deep`
   - lite — build + scan (expected, when there are already existing artifacts)
   - normal — build + scan + custom approximations
   - deep — build + scan + custom approximations + custom rules
   - recommend by what's on disk: a cold start (no `.opentaint` artifacts) → deep; a prior run's artifacts already present → lite
2. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — static + PoC per confirmed TP. This launches a few test services on the user's machine (local instances and ports), torn down at the end of the run. Make that clear in the option

### 5. Bootstrap

Seed the run state and the working tree with the chosen levels and language:

```bash
uv run <skill-dir>/scripts/generate.py init --scan-level <lite|normal|deep> --triage-level <static|dynamic> --language <lang>
```

It writes `state.yaml` with `mode: assessment`, appends this pass to `history.yaml`, and creates the `.opentaint/` tree.

Over a tree an earlier pass already built, it prints what carried over and keeps all of it — an enactment pass's boundary-derived rules, its approximations, and its verdicts are this pass's starting corpus, and `get_status.py` will report their phases `DONE` rather than redoing them.
