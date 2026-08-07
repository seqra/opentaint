# Baselines, suppressions, and CI gating

OpenTaint lets you adopt static analysis on an existing codebase without
drowning in the findings that were already there, and without hiding anything
silently. This guide covers three related capabilities:

- **Baselines** — compare a scan against a previous report and tell what is new.
- **Suppressions** — record an explicit human decision to accept or defer a finding.
- **Gating** — fail a build on findings, optionally only on new ones.

Everything is expressed in [SARIF 2.1.0](https://docs.oasis-open.org/sarif/sarif/v2.1.0/)
using the format's own fields, so any SARIF-aware tool (GitHub code scanning,
GitLab, IDEs) understands the output.

## The mental model: two independent axes

A finding sits on two axes that never interfere with each other.

| Axis | Question | Where it lives | Set by |
|------|----------|----------------|--------|
| **Baseline state** | *Is this new?* | `result.baselineState` | `--baseline` comparison |
| **Suppression** | *Did a human accept this?* | `result.suppressions[]` | `opentaint triage` |

The two are orthogonal. A finding can be old **and** unaccepted (it shows up as
`unchanged` and still counts). It can be new **and** already suppressed (rare,
but valid). Nothing about being in the baseline makes a finding "accepted" — only
a `triage` decision does that.

Neither axis ever deletes a result. Suppressed and baselined findings stay in the
report, marked; the CLI filters them at display and gate time, not in the file.

## Quick start

```bash
# 1. Scan once. Keep the report — it is your baseline.
opentaint scan -o baseline.sarif .

# 2. In CI, scan against it and fail only on new findings.
opentaint scan --baseline baseline.sarif --error-on-findings .
```

That is the whole ratchet: a codebase with 40 pre-existing findings does not turn
CI permanently red — only work introduced by the current change fails the build.

## The lifecycle

### 1. Establish a baseline

A baseline is just a SARIF report you saved. There is no separate baseline
format and no suppressions file to maintain.

```bash
opentaint scan -o baselines/main.sarif .
```

Commit that report (or store it as a CI artifact keyed to your default branch).

### 2. Triage the findings you have reviewed

`opentaint triage` records a decision about a finding directly in the report.
Two verdicts, each requiring a justification:

```bash
# "Won't fix" — reviewed, accepted as not a real risk here.
opentaint triage baselines/main.sarif \
    --accept q3Vf9k --justification "MD5 is a cache key, not a secret hash"

# "Not fixing yet" — real, but deferred.
opentaint triage baselines/main.sarif \
    --defer 8bc1d2 --justification "scheduled with the payments refactor (PAY-1420)"
```

A finding is named by a **fingerprint prefix**, git-style — the value shown as
`Fingerprint:` by `opentaint summary --show-findings`. An ambiguous or unknown
prefix is an error, never a guess. `--accept`, `--defer`, and `--unsuppress` are
repeatable; one `--justification` applies to every decision in the invocation,
and passing it twice is an error rather than a silent "last one wins" — run
`triage` once per reason.

Each decision is written as a SARIF suppression (see
[Suppression reference](#suppression-reference)):

```json
"suppressions": [{
  "kind": "external",
  "status": "accepted",
  "guid": "3f2a…",
  "justification": "MD5 is a cache key, not a secret hash"
}]
```

### 3. Decisions travel forward

When a later scan runs with `--baseline`, a current finding that matches a
baseline entry carrying a suppression **inherits it verbatim** — same status,
same justification, same guid. A decision is authored once and re-attached by
every scan afterwards, for as long as the finding's fingerprint still matches.
When the code is fixed and the finding disappears, its decision retires with it.

This is why suppressions live in the report and not in a config file that would
accumulate dead entries forever.

### 4. Gate CI on new findings

```bash
opentaint scan --baseline baselines/main.sarif \
    --error-on-findings --error-on-severity error,warning -o scan.sarif .
```

With `--baseline`, the gate counts only findings that are **new** and **not
suppressed**. Without a baseline, it counts every reported (non-suppressed)
finding. See [The gate](#the-gate).

### 5. Explain what changed

```bash
opentaint summary scan.sarif --baseline baselines/main.sarif \
    --baseline-state new --show-findings
```

`--baseline-state` here is a **display filter** — it narrows the listing to the
findings in the states you name. This is a different flag from
`scan --write-baseline-state` (see the warning under
[Baseline reference](#baseline-reference)).

## Baseline reference

Given `--baseline old.sarif`, every current finding is classified:

| State | Meaning |
|-------|---------|
| `new` | In this scan, not in the baseline |
| `unchanged` | In both, identical trace |
| `updated` | In both — same source and sink, but the path through the code changed |
| `absent` | In the baseline, gone now (i.e. fixed) |

By default the comparison only affects **what is printed** — the SARIF file is
left byte-for-byte unchanged. Two flags control it:

| Flag | Command | Effect |
|------|---------|--------|
| `--write-baseline-state` | `scan`, `triage` | **Switch.** Persists `result.baselineState` and `run.baselineGuid` into the output report. |
| `--baseline-state <state>` | `summary` | **Filter.** Shows only findings whose state is one of `new` \| `unchanged` \| `updated` \| `absent` (repeatable). |

> **These are two different flags that share the word "baseline-state."**
> On `scan`/`triage` it is a boolean that *writes* the state into the file.
> On `summary` it takes a value and *filters* the listing. They do not overlap.

The filter reads whichever states are available: the ones a previous
`--write-baseline-state` persisted into the report, or the ones a `--baseline`
on the same command line computes on the spot. Both work:

```bash
# states computed now
opentaint summary scan.sarif --baseline main.sarif --baseline-state new --show-findings

# states already in the file, written by the scan that produced it
opentaint scan --baseline main.sarif --write-baseline-state -o scan.sarif .
opentaint summary scan.sarif --baseline-state new --show-findings
```

Asking for a state when the report carries none and no baseline was given is an
error, not an empty listing — "0 findings" would read as a clean bill of health
for a report nobody compared against anything.

`absent` (fixed) findings are never written into the output report — surfacing a
fixed finding as a live alert would be wrong — but `--baseline-state absent`
lists them, read from the baseline, which is how you see what a change fixed.

### Finding identity

Findings are matched across reports by a **fingerprint**, not by line number, so
moving code around does not invent new findings. Three fingerprints exist, from
the most exact identity to the coarsest:

| `--fingerprint-key` | Full key | Hashes | Behavior |
|-----|-----|--------|----------|
| `trace` | `vulnerabilityWithTraceHash/v1` | rule + every step of every trace | Exact; changes if anything on the path moves. |
| `source-sink` | `vulnerabilitySourceSinkHash/v1` | rule + source + sink | Survives edits to the call path between source and sink. **Default.** |
| `sink` | `vulnerabilitySinkHash/v1` | the sink statement alone | Survives a change to where the untrusted data comes from. |

`--fingerprint-key` takes the short name or the full key, and one key governs
everything a command does with fingerprints: baseline matching, the prefix
`triage` resolves, the value `summary --show-findings` prints as `Fingerprint:`,
and what `--partial-fingerprint` matches. That is why a fingerprint copied off
the screen always names a finding to `triage`. (`--partial-fingerprint-key` is a
deprecated alias for `--fingerprint-key`.)

The source→sink hash is the default because a decision should survive
refactoring of an unrelated helper the flow happens to pass through. The finer
trace hash is what distinguishes `unchanged` from `updated`.

Choose `sink` when you care about the vulnerable statement rather than how data
reaches it — one decision on `Runtime.exec(cmd)` then covers every route into it,
and stays put when a new caller adds another one. It is the coarsest identity, so
it also merges the most: several findings that differ only in their source become
one entry, and suppressing it suppresses them all. All three hash the rule id, so
no fingerprint ever spans two rules that fire on one statement.

Comparing reports built with different fingerprint keys is a hard error, not a
silent zero-match. Findings that carry no fingerprint at all (a report produced
without fingerprints) are reported as-is and counted as "not comparable."

## Suppression reference

A suppression is written only by `opentaint triage`, only with a justification,
and only ever as `kind: "external"` (the justification lives outside the source,
not in an in-source comment). The verdict is carried by the SARIF `status`:

| `triage` flag | `suppression.status` | Meaning | Hidden from gate? |
|---------------|----------------------|---------|-------------------|
| `--accept` | `accepted` | The team will not fix this | Yes |
| `--defer` | `underReview` | The team is not fixing this for now | Yes |
| `--unsuppress` | *(removes the entry)* | Retract a decision | — |

Both `--accept` and `--defer` hide the finding from the listing and from the
gate. A deferral does **not** expire on its own; the summary's `Deferred` count
keeps it visible so it can be revisited.

`--unsuppress` removes the suppression from the report being triaged. It does not
"un-inherit": if the baseline still carries the decision, the next scan re-attaches
it. To retract a decision permanently, re-triage the baseline.

### Reading suppressions conservatively

When a baseline (or a report from another tool) is read, its suppressions are
interpreted defensively:

| Status on the entry | Outcome |
|---------------------|---------|
| absent, or `accepted` | Suppressed |
| `underReview` | Suppressed, counted as deferred |
| `rejected` | **Not** suppressed — the suppression was explicitly denied |
| anything unrecognized | **Not** suppressed, counted under "Not honored" |

A non-accepted or unknown status never hides a finding, and never disappears
silently — the summary surfaces it.

> **Note on false positives.** SARIF 2.1.0 has no formal false-positive marker,
> and `status: "rejected"` means "the suppression request was rejected" (report
> it), not "this finding is wrong." Record that a finding is a false positive in
> the free-text `--justification`.

### The summary Suppressions group

```
Suppressions
├─ Suppressed: 14 of 90
├─ Won't fix: 9            (accepted)
├─ Deferred: 5            (under review)
├─ Inherited from baseline: 12
└─ Added this run: 1      (triage only)
```

`opentaint summary --show-findings` hides suppressed findings by default; add
`--suppressed` to list them with their justification.

## The gate

| Flag | Meaning |
|------|---------|
| `--error-on-findings` | Enable the gate. Off by default — without it, scans never fail on findings. |
| `--error-on-severity <levels>` | Restrict the gate to these levels: `error`, `warning`, `note`, `none`. Comma-separated or repeated; default is all reported levels. |

A finding counts toward the gate when it is **not suppressed** and its level is
in scope. With `--baseline`, only **new** findings count (`unchanged` and
`updated` existed before). Findings that cannot be compared (no fingerprint) fail
closed — they count.

### Exit codes

| Code | Meaning |
|------|---------|
| `0` | Completed; gate not tripped |
| `2` | Findings remain and `--error-on-findings` was set |
| `1` | General failure (bad input, unreadable report) |
| `252`–`255` | Analyzer failure (exception, OOM, timeout, config error) |

Exit `2` is deliberately distinct from `1` and from the analyzer codes, so CI can
tell "the scan found new problems" apart from "the scan itself broke."

## Rule selection (a related scan-time control)

Rule selection decides which rules the analyzer runs at all. It is **not**
suppression: an excluded rule never loads, so it produces nothing in the report
and there is nothing to review later. To hide a finding a rule *did* produce,
accept it with `triage` instead.

Configure allow/deny lists in the config file:

```yaml
rules:
  only:                          # if set, only these rules run
    - sql-injection              # exact rule name
    - java/security/**           # glob over the full id
  exclude:                       # these rules never run
    - reflected-xss-in-servlet-app
```

Or on the command line:

```bash
opentaint scan --exclude-rule-id java-jwt-decode-without-verify .
```

Each entry matches a full `path/to/file.yaml:rule-id`, a bare rule name, or a
doublestar glob over the full id — the same grammar as `summary --rule-id`.
`--rule-id` overrides the config lists; `--exclude-rule-id` overrides
`rules.exclude`.

Notes:
- Excluding a rule does not fake a wave of fixes. A baseline finding whose rule
  did not run in the current scan is reported as `Rule not run`, separately from
  `Fixed`, because its absence says nothing about whether anyone fixed it.
- A pattern matching no rule produces a warning, so a typo cannot silently look
  effective.
- A selection that ends up matching **no** rules is an error, not a silent scan
  of nothing — `--dry-run` reports it without compiling.
- Excluding a library rule that a surviving rule joins against keeps working: the
  reference still resolves, so removing a rule never quietly breaks another.

## CI/CD recipes

The official [GitHub Action](https://github.com/seqra/opentaint/tree/main/github)
and [GitLab template](https://github.com/seqra/opentaint/tree/main/gitlab) wrap
`opentaint scan`. Baseline gating is driven by the CLI directly, as shown below.

### GitHub Actions

Persist the default-branch report with `actions/cache`, restore it on pull
requests, and gate on new findings. A cache written on the default branch is
readable from pull-request runs via `restore-keys`, which makes it a simple,
official way to carry the baseline forward. (The first run has no baseline and
scans without gating; every later PR gates against the latest main report.)

```yaml
name: opentaint
on:
  push:
    branches: [main]
  pull_request:

jobs:
  scan:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install OpenTaint
        run: curl -fsSL https://raw.githubusercontent.com/seqra/opentaint/main/scripts/install/install.sh | sh

      # Restore the most recent main baseline. On main, this key also becomes
      # the save target below; on a PR, restore-keys falls back to it read-only.
      - name: Restore baseline
        uses: actions/cache@v4
        with:
          path: baseline.sarif
          key: opentaint-baseline-${{ github.run_id }}
          restore-keys: opentaint-baseline-

      - name: Scan
        run: |
          if [ -f baseline.sarif ]; then
            opentaint scan --baseline baseline.sarif \
              --error-on-findings --error-on-severity error,warning \
              -o opentaint.sarif .
          else
            opentaint scan -o opentaint.sarif .
          fi

      # On main, the fresh report becomes the next baseline.
      - name: Update baseline
        if: github.ref == format('refs/heads/{0}', github.event.repository.default_branch)
        run: cp opentaint.sarif baseline.sarif

      # Optional: send to GitHub code scanning (suppressions & states are honored).
      - name: Upload SARIF
        if: always()
        uses: github/codeql-action/upload-sarif@v3
        with:
          sarif_file: opentaint.sarif
```

The `cache@v4` step saves `baseline.sarif` under `opentaint-baseline-<run_id>`
at job end, so each main run leaves a fresh baseline that the next PR restores
via the `opentaint-baseline-` prefix.

### GitLab CI

```yaml
opentaint:
  script:
    - curl -fsSL https://raw.githubusercontent.com/seqra/opentaint/main/scripts/install/install.sh | sh
    - |
      if [ -f baseline.sarif ]; then
        opentaint scan --baseline baseline.sarif \
          --error-on-findings --error-on-severity error,warning \
          -o gl-opentaint.sarif .
      else
        opentaint scan -o gl-opentaint.sarif .
      fi
  artifacts:
    when: always
    paths:
      - gl-opentaint.sarif
```

Keep the main-branch `gl-opentaint.sarif` as the `baseline.sarif` for later
pipelines (via the package registry, a cache key, or a committed artifact).

## SARIF conformance

Every annotation is a standard SARIF 2.1.0 field, so third-party tools ingest the
report without OpenTaint-specific knowledge:

- **§3.35 `suppression`** — `kind` (`external`), `status` (`accepted` /
  `underReview`), `justification`, `guid`.
- **§3.27.24 `result.baselineState`** — `new` / `unchanged` / `updated` /
  `absent`, written under `--write-baseline-state`.
- **§3.14.5 `run.baselineGuid`** — cites the baseline run's
  `automationDetails.guid`, so the report is itself citable as a future baseline.

No property bag or vendor extension is required for any of it.

## See also

- [Usage Guide](usage.md) — full command and flag reference (`scan`, `triage`, `summary`).
- [Configuration Guide](configuration.md) — the `rules.only` / `rules.exclude` config keys.
