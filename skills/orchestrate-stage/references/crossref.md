# Cross-reference — scan results against the reference set

Judge, per supplied finding, whether the latest scan reproduced it, and assemble the coverage manifest. Enactment mode only, and the stage that closes the run: every rule, approximation, and verdict is already in place, so what the scan shows now is what the run delivered. Nothing else may set a reference finding's `status`.

It is also the stage that decides what the run still owes. A judgement here can send the pipeline back — an unmodeled carrier to an approximation round, a rule-caused miss to the stage that authored the rule — and status will report that earlier phase as current again. That is the loop working; re-enter this stage after the rescan rather than closing on stale results.

## Match by identity, never by rule id

For each reference finding `get_status.py` lists as pending, compare the scan's results against its recorded identity: the source the trace enters at, the propagation it goes through, the sink it reaches, and the location. A result counts as a reproduction only when its trace carries the same attack path. A rule firing somewhere, a matching vulnerability class, or a matching file is not a match.

Record the outcome on the reference file:

`.opentaint/tracking/reference/<finding-id>.yaml` — one supplied finding, normalized to a stable identity and carried through boundary discovery and the cross-reference. The file is named for the finding's own id. `family` ties it to its boundary spec and is rewritten when a family splits. `status` is `pending` until the cross-reference judges it, then `reproduced` or `unreproduced`; `cause` explains an `unreproduced` one so the pipeline knows who owns it — `rule` (a boundary, restriction, or sanitizer is wrong), `approximation` (an opaque carrier breaks the path), or `engine` (a modeling limit, paired with `blocker`). `blocked_at` lists the carriers still to model and is cleared once they are modeled or judged terminal. `matched_hashes` are the SARIF result hashes whose trace carries this finding's identity — never a rule-id match alone. Keep it clear from comments

```yaml
id: DSC-014
vuln_class: ssrf
family: ssrf
source: request body field `callbackUrl` on POST /api/webhook/register
propagation: WebhookReqVO -> WebhookDO -> WebhookService#dispatch
sink: RestTemplate#getForObject in WebhookService#dispatch
expected_location: yudao-module-infra/.../WebhookService.java:88
guards: URL parsed with new URI(...), no private-range rejection
status: reproduced
cause: null
blocker: null
blocked_at: []
matched_hashes: [a1b2c3d4e5f6a7b8]
crossref: done
notes: >
  crossref: join ssrf-webhook-ext fired at WebhookService#dispatch:88 with the trace entering at
  the registration body — same attack path as the reference finding
```

- reproduced — set `status: reproduced` and put the matching SARIF result hashes in `matched_hashes`
- overmatch — the trace reproduces, but the same rule also fires on flows that are not this finding: still `reproduced`, and note the overmatch in `notes`
- stops at an opaque carrier — `status: unreproduced`, `cause: approximation`, and the exact carrier(s) in `blocked_at`. Get the carrier from `.opentaint/results/dropped-external-methods.yaml` or a localized reachability trace, not from a guess
- no source or sink fact on the expected path — `status: unreproduced`, `cause: rule`. Say in `notes` which side is missing and why, and report it to MAIN: the stage that authored the rule fixes it and the run comes back here
- reproducible only by a modeling limit the engine cannot express — `status: unreproduced`, `cause: engine`, one-line `blocker`, and `blocked_at` cleared

Set `crossref: done` on every file you judge. A later rescan makes them pending again, which is the loop working: judge them against the new results rather than trusting the old verdict.

Independently, note scan results that carry no reference finding — those are OpenTaint-exclusive and go to triage like any other finding. Do not count them as reproductions.

## Close the blocked carriers

When `get_status.py` reports traces stopping at unmodeled carriers, that work belongs to an approximation round, not here: report the carriers to MAIN, which runs the round and the rescan and re-enters this stage. Only after the rescan proves a carrier still breaks the path does it become an `engine` cause with a `blocker`.

## Write the coverage manifest

Once no reference finding is pending or blocked, rewrite `.opentaint/enactment.md` from the current reference files:

- the finding-level coverage table — one row per supplied finding: id, vulnerability class, family, `status`, and the one-clause reason for an unreproduced one
- the three counts kept apart: raw SARIF results, validated findings, unique vulnerability identities
- reproduced, OpenTaint-exclusive, and reference-exclusive findings as separate sections, exclusives only when triage validated them
- the reusable artifacts the run produced: source rules, sink rules, joins, approximations
- one blocker line per non-reproduced finding, naming the rule, modeling, or engine limitation that remains

Reflect only current state — rewrite the manifest, don't append to it.

## Stage gate

`get_status.py` names pending reference findings, blocked carriers, then the manifest. Finish when `crossref` is `DONE`. Report reproduced/unreproduced totals and every blocker.
