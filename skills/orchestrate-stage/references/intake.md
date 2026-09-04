# Intake — this mode's input, as the run's families

Turn what the pass was given into the families the boundaries stage generalizes. The three modes start from different material and converge on the same handoff: a named family per group, each carrying the evidence it was grouped from. Nothing here authors a rule, proposes a boundary, or touches a model.

Read `mode` from `get_status.py --full` and follow that mode's section. A family is the set of evidence you expect to share one universal source and one universal sink — partition by vulnerability class or by a cohesive attack surface, never by file batches or arbitrary count.

## Onboarding — the external-method frontier

Every dependency member the project's own code calls is a trust boundary until a leaf says otherwise. That over-approximation is the point: the sweep classifies the whole frontier once, and every later pass inherits the verdicts.

### 1. Triage the dependencies

Dispatch triage-dependencies when status names it.

Expect back — `.opentaint/tracking/coverage.yaml` written with the flagged packages; status advances to the frontier partition.

### 2. Partition the frontier

Run:

```bash
uv run <skill-dir>/scripts/generate.py partition frontier
```

It writes balanced `.opentaint/tracking/rules/plans/lib-NNN.yaml` plans over the flagged packages' members the project actually calls, one disjoint slice per leaf. On re-entry it partitions only members no prior pass verdicted.

### 3. Sweep it

Fan out discover-attack-surface, one per plan.

Inputs each:
- `language`
- `plan`

At the join run:

```bash
uv run <skill-dir>/scripts/generate.py mark-safe
```

Expect back — each leaf records the trust boundaries it finds into its plan and writes any source unit(s); the join folds source/safe verdicts into `classification.yaml` and prunes the consumed plans. The sweep is a single fan-out pass, not a loop.

### 4. Group the frontier into families

Read the verdicted boundaries back from the ledger and the source units the sweep wrote, and group them into families — usually one per attack surface a set of members shares (a framework's request accessors, a client library's egress calls), not one per dependency. Write them to `.opentaint/tracking/scope.yaml`, evidence being the members themselves.

`.opentaint/tracking/scope.yaml` — what this pass's intake scoped, and the families the boundaries stage generalizes one at a time. `scope` is one line on what the pass was given, so a later reader knows what the family list came from. Each family carries the `evidence` it was grouped from: the frontier members a sweep verdicted, or the members, endpoints, and code areas a diff or spec resolved to. Enactment mode writes no scope file — its families live on the reference findings, which carry the same assignment on the file that moves with them. Keep it clear from comments

```yaml
mode: discovery
scope: docs/2026-07-webhooks.md — partner webhook registration and delivery
families:
  - name: ssrf-webhook
    evidence:
      - com.acme.webhook.WebhookController#register
      - com.acme.webhook.WebhookService#dispatch
  - name: upload-path
    evidence:
      - com.acme.upload.UploadController#store
```

## Discovery — the project, a diff, or a spec

`state.yaml` names the scoping document under `spec` when there is one; with none, the scope is the whole project.

Resolve the input to code before grouping it: read the diff or spec, then the project source it points at — the endpoints, handlers, jobs, and consumers it touches, and the calls they make into dependencies. An informal spec ("this service takes uploads from partners and renders them") is scoped the same way: name the surfaces it implies and read them.

Then group what you read into families and write `.opentaint/tracking/scope.yaml`, evidence being the members, endpoints, or code areas each family was grouped from — concrete enough that the boundary leaf can go straight to the source.

Fan this reading out when the scope is large: one leaf per slice, each reporting the surfaces it found. Assign the families yourself once every slice has reported, since that decision needs the whole scope.

`.opentaint/tracking/scope.yaml` — what this pass's intake scoped, and the families the boundaries stage generalizes one at a time. `scope` is one line on what the pass was given, so a later reader knows what the family list came from. Each family carries the `evidence` it was grouped from: the frontier members a sweep verdicted, or the members, endpoints, and code areas a diff or spec resolved to. Enactment mode writes no scope file — its families live on the reference findings, which carry the same assignment on the file that moves with them. Keep it clear from comments

```yaml
mode: discovery
scope: docs/2026-07-webhooks.md — partner webhook registration and delivery
families:
  - name: ssrf-webhook
    evidence:
      - com.acme.webhook.WebhookController#register
      - com.acme.webhook.WebhookService#dispatch
  - name: upload-path
    evidence:
      - com.acme.upload.UploadController#store
```

## Enactment — the supplied finding set

`state.yaml` names the supplied findings under `findings` — a manifest, SARIF, report, or directory of finding documents. Write one `.opentaint/tracking/reference/<finding-id>.yaml` per supplied finding.

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

Give each finding a stable id of its own — the supplied one when it has one. Preserve separately triggerable attack paths as separate findings even when they share a sink. Never drop a finding for being a poor fit for taint analysis: an authorization, integrity, configuration, hard-coded-secret, or structural-control finding gets a reference file like any other, and becomes an explicit pseudo-boundary later.

Then group the findings into families and set `family` on each. Enactment's families live on the reference files themselves rather than in `scope.yaml`, because the assignment has to move with the finding when a family splits.

Fan out this normalization when the supplied set is large: one leaf per slice of the supplied report, each writing its own reference files. Assign the families yourself once every file exists, since that decision needs the whole set.

## Stage gate

`get_status.py` drives `intake`, naming the mode's next step — the dependency triage, the frontier plans, the scope file, or the findings still without a family. Finish when it reads `DONE`, or when the next step it reports is the boundaries stage.
