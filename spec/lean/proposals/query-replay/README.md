# Newly authorized summary replay

**Proposal model. The runtime optimization is not implemented.** This directory proves a finite authorization filter for replay after new current-query admission. It does not remove StrongQueries or change AP, field, source, cleaner, record or query-admission semantics.

The source reference is `fcfe2e90558665d813bd74207832d4ae3fc83aec`, core `57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`. The original model and audit are copied unchanged from the external investigation. Its earlier receipts and failed attempts remain in the `correlated-concrete-20261026/validation/next-query-replay-model` campaign directory.

## Source boundary

The relevant source files are under `core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`:

| Source | Reference behavior |
|---|---|
| `engine/StrongQueries.kt`, `admit` | Install the complete fresh batch before any returned initial executes |
| `engine/StrongQueries.kt`, `permits` | Require every complete nonzero premise member; ZERO needs a nonempty admitted set |
| `engine/RunMethodAnalyzer.kt`, `addLink` | A nonempty admission currently scans every raw summary and queues each permitted result |
| `engine/RunMethodAnalyzer.kt`, `queuePublications` and `published` | Regular raw deltas have their own publication path; backward ZERO already publishes without current-query permission |
| `store/RunSummaries.kt`, `borrow` | Borrow current raw rows under the exact complete premise |

The model uses a decidable type for canonical initial identities. Lists denote finite sets by membership. `admit` returns duplicate-free identities absent from the old set. It does not model AP matching or derive canonical initials from actual facts.

## Result

Let Q be the old admitted set, F the disjoint fresh batch and P one complete premise. Permission changes from false to true exactly when:

```text
P intersects F, and every member of P belongs to Q union F.
```

The model has 24 theorem declarations:

* `transition_fresh_witness` uses an executable finite search to return a member of P and F. It needs no Classical choice.
* `newly_authorized_iff` proves the exact permission transition above.
* `unary_exact_borrow` proves that a unary premise becomes authorized exactly when its initial is fresh.
* `candidate_membership`, `candidate_once`, `replay_exact` and `replay_once` prove complete candidate selection and one replay per tuple, including a tuple found through two fresh members.
* `complete_nd_required` rejects a tuple with a missing member. Unrelated admissions and old permitted tuples need no authorization backfill.
* `backward_zero_no_backfill` and `forward_zero_first_nonempty` prove the separate ZERO cases. Forward ZERO backfill occurs only at the first nonempty admitted set.
* `annotation_not_authorization` preserves the distinction between authorization replay and regular raw deltas. Equal ordinary content with a new protection annotation still needs its normal delta delivery.

Candidate enumeration is a mathematical specification. It does not require a new runtime index or prescribe the model's simple list-based deduplication as a production algorithm. ND members authorize one complete tuple; they do not become independent alternatives.

`cumulative_replay_equivalent` is conditional: the current complete snapshots of previously authorized tuples must already be visible, including regular raw and late-annotation deltas. Under that assumption, adding newly authorized tuples gives the same cumulative tuple observations as replaying all permitted tuples. This directory does **not** prove that delivery assumption for the engine. It proves no whole-engine or source-adapter correspondence, scheduling fairness or performance factor. A broader return to demand-guided FLOW is a separate major semantic proposal.

## Check

From the repository root, run with the cached pinned toolchain:

```sh
python3 spec/lean/proposals/query-replay/check.py
```

The checker can also be invoked by its absolute path from another directory. It discovers the repository root and `lean` on PATH. It requires Lean 4.33.1, uses one Lean worker, pins the child to one CPU where supported, caps Lean memory at 768 MiB and applies a 60-second limit to each command. It starts no Gradle, JVM or project analysis.

Outputs and logs go into `spec/lean/.lake/verification/query-replay/`, which the existing Lean `.gitignore` excludes. They are not proof source files and must not be committed. The portable summary is [checks.json](checks.json); source paths in that receipt are relative to the repository root. Original command paths and logs remain in the ignored verification directory or external campaign history.

Fifteen executable controls cover fresh-set deduplication, partial/complete ND, two fresh members finding one tuple, unrelated admission, an already permitted tuple, executable witness selection, exact unary borrow, both ZERO directions, late annotation and a repeated protected offer. [Audit.lean](Audit.lean) checks all 24 theorems and 13 pure definitions: 37 declarations in total. Only `propext` and `Quot.sound` are accepted; no `Classical.choice`, `sorryAx` or custom axiom is accepted. The IO control runner is executed separately.

The receipt records hashes of the current source-reference files for review. Those hashes do not turn this finite model into an implementation proof. The runtime-to-model adapter and preservation of regular raw-delta delivery remain implementation obligations before this optimization can be enabled.
