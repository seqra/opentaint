### 1. Confirm the toolchain

Confirm `opentaint` is on PATH with `opentaint -v`. If it's missing, don't proceed silently — tell the user and offer the install command for their platform, run an install only on explicit confirmation:

- macOS / Linux, in order: `brew install --cask seqra/tap/opentaint` · `npm install -g @seqra/opentaint`
- Windows: `npm install -g @seqra/opentaint`

After installing, run `opentaint health` to confirm everything's resolved.

### 2. Confirm agent nesting

This workflow requires two subagent levels: MAIN → stage orchestrator → leaf. Confirm the harness permits depth 2 before starting; otherwise ask the user to enable it.

### 3. Choose the mode and locate its input

Pick `onboarding`, `discovery`, or `enactment` per Modes, confirm the choice with the user, and get the path its intake needs — the supplied findings for enactment, the diff or spec for discovery when there is one. Onboarding needs no input beyond the project.

### 4. Determine the language

Read the project's build files to fix the target language — Maven/Gradle → java, `go.mod` → go, and so on. Record it at bootstrap; stage orchestrators pass it to language-coupled leaves. When a repo carries build markers for more than one, ask the user which to analyze.

### 5. Choose the workflow

Ask the user for the knobs this mode has, together:

1. Scan level — `lite` · `normal` · `deep`, **discovery mode only**
   - lite — build + scan (expected, when there are already existing artifacts)
   - normal — build + scan + custom models
   - deep — build + scan + custom models + custom universal rules
   - recommend by what's on disk: a cold start (no `.opentaint` artifacts) → deep; a prior pass's artifacts already present → lite
   - onboarding and enactment are always deep: sweeping the frontier and reproducing a finding set both need the full rule and model toolbox, so there is no level to ask for
2. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — static + PoC per confirmed TP. This launches a few test services on the user's machine (local instances and ports), torn down at the end of the run. Make that clear in the option

### 6. Bootstrap

Seed the run state and the working tree:

```bash
uv run <skill-dir>/scripts/generate.py init --mode <onboarding|discovery|enactment> \
  --triage-level <static|dynamic> --language <lang> \
  [--scan-level <lite|normal|deep>] [--findings <path>] [--spec <path>]
```

`--scan-level` is discovery's; `--findings` is enactment's and required the first time; `--spec` is discovery's and optional. It writes `state.yaml`, appends this pass to `history.yaml`, and creates the `.opentaint/` tree — plus `tracking/reference/` in enactment mode.

Over a tree an earlier pass already built, it prints what carried over and keeps all of it — that pass's rules, models, boundary specs, and verdicts are this pass's starting corpus, and `get_status.py` will report their phases `DONE` rather than redoing them. It refuses a second onboarding pass over an already-onboarded tree.
