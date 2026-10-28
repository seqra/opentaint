# Restricted demand: selected repair checks

Date: 28 October 2026. Status: **partial implementation; not accepted**.
Source: `86eb2f04377a9cef7648b1c1152f9c55da182787` plus uncommitted runtime
changes. The contract is
[restricted-demand-static-closure.md](../../spec/restricted-demand-static-closure.md).
This is not a landed-commit performance report.

No project scan has started. The last referenced Thingsboard campaign
reached **run-2**, completed **run-1**, and accepted **run-1**. The local
transition controls below reach and complete **run-3**. Five still lose
the final finding because killed-write handoff is not implemented yet.

## Selected changes and evidence

| Check | Result | What it establishes |
|---|---|---|
| Abstract STAR demand normalization | 95 focused tests pass | Entry/exit Empty E, shared FLOW start, scalar/packed agreement, unchanged concrete/actual/native E and protection |
| New exclusion tests before/after fix | Nine tests: seven fail before, none fail after | The new behavior is checked rather than inherited from the old oracle |
| Abstract demand local model | 19 constructive audits pass | Demand widening/idempotence, C2 against normalized demand, C5 raw-pair/layer preservation and actual-E matching |
| Static STAR input correction | 44 focused tests pass | Named-field STAR/E relay, no-demand/no-start, actual mark gate, bounded paths and retained negative grammar checks |
| Static input local model | 15 constructive audits pass | Grammar extension, bounded STAR identity/limit relay under explicit adapters |
| Immediate write supply and relay removal | 26 focused tests pass | Actual-input/request paths, FULL/GROUP, copy and T-to-U, exit kill, retained FLOW writer, aliases and existing computed summary supply |
| Local write supply model | 14 constructive audits pass | Admission/write witnesses, mark output, FLOW retention, exit independence, idempotent pool union, no new NORMAL record |
| Lost exit-key model | 25 constructive audits pass | Exact pending/final partition, nonmonotone survivors, complete key preservation, seed-only binding and closure transport under explicit adapter contracts |
| Binding scope witness | Six constructive audits pass | Counterexample to exact AP tail-key reassociation; exact closure theorem scoped after bound seeds freeze |
| Current exit/transition controls | 14 tests: nine pass, five fail | Earlier local sink and no-kill controls pass; the separate lost-writer demand family remains unfixed |

The focused suites overlap. Their counts must not be added into a unique
test total. Their XML, commands, logs and source hashes are saved under
`/drive-testcomp/opentaint-go-rules/restricted-demand-20261028`:

- `abstract-demand-focused-checks.json`
- `static-star-domain-focused-checks.json`
- `local-static-supply-focused-checks.json`
- `killed-write-current-red-checks.json`

Proof receipts are beside their models under
`spec/lean/proposals/restricted-demand`. Only `propext` and `Quot.sound`
occur in the combined local audits; there is no classical choice or
unproved placeholder. These are local contracts, not a whole-JVM proof.

## Remaining implementation

Implement the specified thin lost-exit candidate capture, final survivor
pruning and joined writer binding before existing caller inputs release.
Do not disable the five failing correctness tests. Add genuine ZERO
source wrappers and an intermediate exit-generated static write which a
later exit action kills. Preserve ordinary source/sink target grammar:
STAR actual inputs are valid, while a new STAR rule literal is not added.

Run complete local acceptance checks after the implementation is stable.
Commit only after the selected iteration is complete. Then run the four
configured project measurements, reusing baseline `f945f92c5ae554ff4f5fc7696ee5a269210478bb`.
Record engine and transition times, latest reached/completed/accepted run,
finding differences, CPU/heap evidence and candidate/binding/closure work.
Rank the next optimization proposal from those measurements. None of
those project outcomes is claimed by this report.
