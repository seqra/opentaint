# Retained post-handoff demand-row cover

12 November 2026. Generic proof component for the demand campaign. No
production transfer, demand store or stop rule changes. This component does
not classify a corpus row or prove a closed-evolution predicate.

## Guard

Let O be the complete original native demand-row set at the later handoff.
For an individual target X, use K = O minus {X}. For a joint cut R, use
K = O minus R. Keep saved NORMALs and all other state unchanged.

```text
cover(X,K):
    return exists Z in K: C2Check(X,Z)
       and exists Y in K: C5Check(X,Y)

checkCut(O,K):
    return K subset O and every X in O satisfies cover(X,K)
```

These are executable Boolean functions in [RowCut.lean](RowCut.lean).
Witness search returns actual retained rows. A removed row cannot supply
either service, even if several summary origins produced that same row.
The singleton filter removes all occurrences of its exact row. For a joint
plan, check every provider against the same final K.

The reused [kernel](RetainedServiceBasis.lean) checks:

```text
C2Check(X,Z):
    same complete entry owner and equal canonical entry key

C5Check(X,Y):
    same complete owner, physical exit, typed output and output key
    and (equal canonical entry key or pointToMayImage(X.entry,Y.entry))
```

A complete entry owner includes project, full method/context, generated
block and physical entry. Do not merge ports or enclosing methods. The
entry point key unites supported late FULL concrete STAR/EXACT entries at
the same base/path/mark. It excludes FLOW, GROUP, constants and cleaner
temporaries. Legal static anchors need the existing static grammar check.
All other entries stay literal, including control kinds and MAY cursors.

The output key permits only the proved empty-exclusion MAY/STAR selector
equivalence. Keep the complete path, mark, output kind, port and other
coordinates. Point-to-MAY containment supports This, Argument, Return and
LocalVar. Its path difference is empty or CLASS* followed by exactly one
FIELD/ELEMENT. Static and Exception adapters are excluded from that step.
See [the service specification](../../../retained-demand-service-basis.md).

## Proof and controls

`checked_row_reply` uses the existing constructive `split_row_cover` law.
Every reply of X, including its admission/restriction support profile, has
a witness in Z or Y. `checked_cut_oracle_equal` proves equality of the full
row-service union. `checked_all_runs_and_limits` quantifies over arbitrary
later runs, limits, offers, raw packets and shared native programs.
`checked_unbounded_continuation` transports that equality through every
finite continuation. There is no iteration cap or sampled-future premise.

The native adapter remains an explicit proof boundary. The common state
contains saved replay, source permissions, rule contributors, ZERO/Target
routing and other unchanged channels. Their equality must not be assumed
after deleting additional state. Current and later generated state is
handled by the common continuation, not treated as absent.

[RowCutControls.lean](RowCutControls.lean) checks positive split coverage,
both singleton choices, failed joint deletion, missing admission/output
providers, wrong scope, two counted fields, duplicate origins and an absent
provider. A passed generic check alone is not a per-row data certificate.

Run the proof and controls from the repository root:

```sh
python3 spec/lean/proposals/redundant-demand-row-20261112/check.py
```

The script compiles copied dependencies and new proofs in a temporary
directory. It audits actual theorem dependencies and checks operator blobs
at `14d7b63369d94f49d4c551be8405ed7719f267cc`. It does not require the live
checkout to use that old runtime. It does not run Gradle or project scans.
Only `propext` and `Quot.sound` are permitted; no classical choice, assumed
semantic cover, `sorry` or new axiom is used.

## Native correspondence and required binding

The two dependency sources are exact copies of the historical constructive
kernel, pinned by SHA-256 in [check.py](check.py). The historical native
receipt is outside Git:

```text
docs/reports/data/redundant-demand-20261110/cases/
    retained-service-basis-native-v1/receipt.json
```

It pins 11 passed native tests of direct/prepared C2/C5, complete ND packets,
typed controls, support profiles, loop consumers and literal native rows.
Its SHA-256 is
`c8093cda966e140ec70d47aa94121be7de92f1136c06fb879b63297f21694e53`.
Those historical tests are supporting correspondence evidence. This new
component reruns Lean, not the native tests or original scans. The checker
also rechecks all 27 native artifact hashes, eight input pins, six operator
pins and the XML result (11 tests, zero failures/errors/skips). The recorded
test checkout has the same complete `core/model/rules/scripts` source tree
as the pinned runtime. Test source, compiled test jar, complete native input
data and observed metrics are bound to that receipt. The row-cut change
does not change an operator: it changes only which complete row witnesses
remain available. Use the external archive from
[the evidence policy](../../../../docs/reports/EXTERNAL_DATA.md) for this
native receipt audit.

`bind_observed.py` writes the finite observed binding outside Git. It
decodes complete original row identities and actual stored accessor kinds,
then compiles every selected X/Z/Y guard in small Lean batches. It checks
distinct original row keys, not distinct origin keys. The complete original
key dictionary, relevant native rows, numeric codebook, exact triple table,
generated Lean, compiled objects, logs and input hashes stay together.
The separate reviewer must rederive the codebook from the native snapshots.

`ObservedRowGuards.checked_actual_classifier` transports a proved guard
from the finite test classifier to any actual classifier that agrees on
the stored X-entry fields. Classification of every future field remains
arbitrary. `checked_services` connects the observed guard to `checkRow`;
the generic row-cut proof then supplies the unbounded consequence. The
finite check itself is not a future-completeness assumption. Corpus
acceptance additionally requires the independent original-state and data
binding checks. This tool changes no ledger status.

Bind each new certificate as follows:

1. Reconstruct O from the native demand after ordinary handoff, not from
   one origin's projected contribution. Check every merged producer.
2. Decode full literal rows injectively. Assign one native key to one
   retained row. Two origins of an identical row have the same row key.
3. Bind owner, ports, base constructors, full marks, all exclusions,
   typed controls and the complete output-selector key. Preserve literal
   protection/packet state where it exists. No additional JVM type guard.
4. Verify the actual accessor classifier for all stored guard paths.
   Future fields stay arbitrary; do not default unknown fields to CLASS.
5. Check actual retained Z/Y membership in K, with complete keys. A
   different origin of deleted X is not a retained row witness.
6. Keep the native support profiles and relative budgets from the existing
   adapter. Do not change sources, sink identity, layers or stop behavior.

For origin certificates, removing X's origin can leave its row in O. This
proof instead removes the entire row. Old origin classifications therefore
need a fresh binding; their counts are not row-level classifications.

## Closed evolution: current limit

The existing NORMAL replay pattern requires a complete source/CFG copy
graph. Those eligibility guards are outside the current edge-only contract.
It cannot classify a row merely because that graph was checked earlier.

No existing checked closed-evolution predicate follows from X -> Y -> X.
Finite demand, summary and input equality does not exclude a later new
field or offer. A repeated row can still deliver a known summary to a new
context. A future predicate needs a constructive closure invariant over
all permitted inputs, field limits, producers and outgoing branches, with
an independent retained route. The current proof is coverage/subsumption;
it does not claim that its retained representative stops repeating.

Historical latest reached/completed/accepted forward runs remain OWASP
run-11/run-11/run-11, Conductor run-8/run-7/run-7 and Stirling-PDF
run-11/run-10/run-9. This proof adds no project iteration.
