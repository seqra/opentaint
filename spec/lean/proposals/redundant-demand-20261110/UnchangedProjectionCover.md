# Unchanged projection cover

10 November 2026. This is a new campaign predicate, not an extension of P.
It changes no production code. Its proof concerns guidance construction after
a completed later forward barrier. Keep the earlier run unchanged.

## Predicate and behavior

Let O contain every final outgoing scalar membership at the later barrier.
Keep full ND premises and protected/plain identity in O. Let U be the fixed
repeated target set for that project and barrier. Let pi(e) be the complete
set of normalized paired demand rows that the real handoff emits from e.

```text
UnchangedProjectionCover(X, O, U):
    require X in O and X in U
    for each q in pi(X):
        save an actual anchor Y with:
            Y in O
            Y not in U
            q in pi(Y)
    accept only if every q has such a checked anchor
```

The anchor can differ for each q. It must come from the same actual barrier,
not another project, execution or future run. All origins outside U remain
fixed. No accepted predicate in this campaign can remove an anchor.

| Part | Current | Proposed |
| --- | --- | --- |
| Demand insertion | Every outgoing origin inserts its projections | Skip only X's insertion when the predicate passes |
| Final demand store | Contains every normalized pair after deduplication | Contains exactly the same pairs through retained anchors |
| Raw facts/summaries and ND grouping | Existing current-run stores | Unchanged |
| NORMAL persistence, reports, seeds and source hits | Existing separate stores | Unchanged |
| Rules, matching, C2, C5, static handling and field limits | Existing behavior | Unchanged |

This is not raw summary subsumption. In particular, it does not collapse a
protected edge with an unprotected edge, or a MUST relation with a MAY
relation. Those raw relations remain distinct. The predicate uses equality
of their actual normalized next-run projections only.

The selected Conductor example, after **run-7**, is:

```text
X: arg(0).MapKey.*/T -> ret.[any]/T,
   DEMAND, protected, repeated at run-5/run-7
Y: arg(0).MapKey.*/T -> ret.[any-taint]/T,
   DEMAND, protected, present at run-7 and outside U

pi(X) = pi(Y) = (entry ret.[any]/T, exit arg(0).MapKey.*/T)
```

The existing MUST-to-MAY handoff normalization gives that equality. No new
tail or mark rule is introduced. Both rows belong to the same complete
`ParametersUtils.replace` method/context. The full native row keys and actual
anchors belong in the corpus certificate, not this abbreviated display.

## Constructive model

[UnchangedProjectionCover.lean](UnchangedProjectionCover.lean) defines a finite
executable certificate checker. Edge IDs stand for complete raw memberships.
Projection IDs stand for complete normalized paired rows, including full
method/context identity, block and physical ports, endpoint kinds, field
identities, marks and exclusions that survive native normalization.

`validWitness` checks anchor membership in O, absence from U and complete row
membership in the anchor's emission. `check` also checks the target's O/U
membership and every projected row. `checkAll` checks every selected target.
The proof extracts an actual supplied witness for each row; it uses no
classical choice or custom axiom.

For all selected checked targets Q and any other removed subset R of U:

```text
pi((O without R) without Q) = pi(O without R)
```

R and Q can overlap. Every anchor is outside U, so it survives both removals.
If an old row's origin survives Q, keep that origin. Otherwise, its checked
anchor supplies the exact same row. The reverse inclusion follows because
removal cannot add a row. This proves joint safety rather than separate
one-edge claims with circular dependencies.

The model proves equality of every Boolean guidance lookup. It then keeps
the entire other stable state equal and proves exact semantic state equality.
Equal states have equal deterministic future states and observations, and
the same finite nondeterministic traces. Native set-based handoff/query
correspondence must establish that this is the analyzer's semantic state;
the abstract theorem does not verify arbitrary Kotlin code by itself.

The finite native encoding must be injective. `encodedRow` can place a full
canonical row dictionary rank in one opaque coordinate. Its injectivity is
proved. The dictionary must retain the complete native JSON payload, not a
short field name, a mark display or a hash without a checked full-key map.

For observed large domains, O can be `List.range total` and U can be a
contiguous suffix `List.range' cut repeatedCount`. Non-repeated origins get
the first indices. Membership proofs use range bounds instead of reducing a
90,000-element list. `withKnownRows` overrides the captured target and anchor
emissions only. Every other edge's emission remains an arbitrary function
parameter. It is not replaced with an invented empty projection set.

## Guards that cannot be removed

The model includes executable negative examples:

- Two targets with the same row cannot anchor one another. Removing both
  loses that row.
- An anchor in U can be removed by another predicate. It therefore cannot
  justify this predicate, even when it is outside the currently selected Q.
- Covering only one projected ND member does not cover the complete origin.
- A different physical port is a different paired row.
- Separate matches for an entry and an exit do not establish one paired match.
- An absent anchor or a target outside U fails the checker.

Positive fixtures include a retained outside-U anchor, repeated occurrences
of one identical projection, and an empty projection list. An empty list is
safe only when it is the complete real emission, not a failed capture.

These are predicate/kernel fixtures. They are not necessity examples or
project deletion controls, and do not classify corpus occurrences by
themselves.

## Validation and source limits

Repeat all model and axiom checks from the repository root:

```sh
python3 spec/lean/proposals/redundant-demand-20261110/check-unchanged-projection-lean.py \
  --output-directory docs/reports/data/redundant-demand-20261110/receipts/unchanged-projection-cover-lean-v1
```

The receipt checks all **34 theorems**: 20 generic laws and 14 executable
examples. It audits each theorem, not only the final theorem. Dependencies
are limited to `propext` and `Quot.sound`. No `Classical.choice`, proof hole,
custom axiom or native-decide shortcut is used.

The native/source correspondence and full observed certificates are separate
acceptance gates. The proof requires the complete real projection function,
all current raw state and every separate handoff effect to remain unchanged.
It does not authorize suppressing X during analysis, deleting its rule
contributors, changing protection, removing seeds, or removing an anchor.

The source audit must check demand counts/stop behavior, C2/C5 membership,
method and block port reversal, ZERO/Target controls, normalization, source
permissions, reports and NORMAL persistence. Exact projection-set equality
preserves semantic memberships; byte order, allocation IDs and diagnostic
callback counts are not part of this equality.

## Observed finite-domain certificates

[ObservedUnchangedProjectionCover.lean](ObservedUnchangedProjectionCover.lean)
checks all 115 prepared Conductor candidates. It uses the full 93,663-edge
later domain, with 67,877 non-repeated origins before the 25,786-edge repeated
suffix. The known support has 230 complete target/anchor emissions. All other
emissions remain arbitrary parameters, including their future query effects.
The OWASP and Stirling domains are present too, with no selected Q rows.

The generator validates the archived input ledger, every finite edge index,
the complete native projections of the known support, and the injective
115-row full JSON dictionary. It checks 357 observed theorems: 230 known
emission facts, 115 edge certificates and 12 project-level joint results.
All pass with only `propext` and `Quot.sound`. The receipt is
`docs/reports/data/redundant-demand-20261110/receipts/unchanged-projection-cover-observed-v1/receipt.json`.

```sh
python3 spec/lean/proposals/redundant-demand-20261110/generate-projection-cover-observed.py \
  --input-directory docs/reports/data/redundant-demand-20261110/q-unchanged-projection-cover-v1 \
  --output-source spec/lean/proposals/redundant-demand-20261110/ObservedUnchangedProjectionCover.lean \
  --output-directory docs/reports/data/redundant-demand-20261110/receipts/unchanged-projection-cover-observed-v1
```

These checks prepare the occurrence certificates. Only the coordinator can
accept the complete formal/native/source package and change ledger verdicts.
The generator does not modify a ledger, the exported input domain, production
code or the six previously accepted P certificates.
