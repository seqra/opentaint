### 1. Confirm the toolchain

Confirm `opentaint` is on PATH with `opentaint -v`. If it's missing, don't proceed silently — tell the user and offer the install command for their platform, run an install only on explicit confirmation:

- macOS / Linux, in order: `brew install --cask seqra/tap/opentaint` · `npm install -g @seqra/opentaint` · `curl -fsSL https://opentaint.org/install.sh | bash`
- Windows, in order: `npm install -g @seqra/opentaint` · `irm https://opentaint.org/install.ps1 | iex`

After installing, run `opentaint health` to confirm everything's resolved.

### 2. Determine the language

Read the project's build files to fix the target language — Maven/Gradle → java, `go.mod` → go, and so on. You pass it to every language-coupled dispatch, the leaf reads its own reference for it.

### 3. Choose the workflow

Ask the user both levels in a single question tool call — two questions, presented together:

1. Scan level — `lite` · `normal` · `deep`
   - lite — build + scan (expected, when there are already existing artifacts)
   - normal — build + scan + custom approximations
   - deep — build + scan + custom approximations + custom rules
   - recommend by what's on disk: a cold start (no `.opentaint` artifacts) → deep; a prior run's artifacts already present → lite
2. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — static + PoC per confirmed TP. This launches a few test services on the user's machine (local instances and ports), torn down at the end of the run. Make that clear in the option

### 4. Bootstrap

Seed the run state and the working tree with the chosen levels and language:

```bash
uv run scripts/generate.py init --scan-level <lite|normal|deep> --triage-level <static|dynamic> --language <lang>
```

It writes `state.yaml`, seeds `history.yaml`, and creates the `.opentaint/` tree. Then `uv run scripts/get_status.py --full` to see the full pipeline setup and start walking it.
