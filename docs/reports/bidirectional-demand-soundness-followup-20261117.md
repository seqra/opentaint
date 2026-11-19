# Consolidated demand proposal: soundness follow-up

17 November 2026. Synthetic data-flow reachability. FULL marks.
Follow [proof-guide.md](../../spec/proof-guide.md).
[Current consolidated proposal](../design/bidirectional-demand-termination-approach-20261115.md).
Production is unchanged.

**Update:** the [run-2 STAR relay](../design/bidirectional-run2-star-relay-20261117.md)
repairs the gap below. The repaired reference and native adapter preserve
the NORMAL observation and stop naturally at **run-3**. The old rejecting
trace remains a historical control.

**Historical result:** the cleaner repair is part of the consolidated contract. The
continued investigation found a **new proposal soundness gap**, using only
a wrapper and an ordinary field overwrite. Its selected-policy native
adapter stops at **run-3** and loses the observation. The unchanged native
policy retains that observation at run-3.

[Complete new example, per-run annotations and proof](bidirectional-nested-star-soundness-gap-20261117.md).

## 1. Historical issue and current repair

The existing cleaner repair keeps FULL nonstatic FLOW when its whole suffix
region is disjoint from a selected cleaner. Its reference stops at run-3
with its NORMAL observation. The consolidated rule and combined pipeline
now name that transfer explicitly. No further cleaner change is selected.

The new issue is the same-head STAR column of C2:

```text
main -> wrap -> overwrite

overwrite(p) { p.f = new Box(); return p; }
main marks a.g.$/T, calls wrap(a), then checks result.g.$/T; f != g.

run-1 wrap/overwrite: p.*/FLOW -> ret.*/FLOW,D
run-2 root offers ret.g.$/T to wrap
      wrap starts ret.*/FLOW through the existing requested-STAR exception
      wrap offers ret.*/FLOW to overwrite
      overwrite's ret.*/FLOW demand rejects that same-head STAR offer
      no preserving NORMAL summary is learned
run-3 no service/demand remains for the call; the real g observation is lost
```

All paths fit limit 1; no NE cut, cleaner, configured pass, loop, recursion,
static or ND join is involved. This demonstrates a separate G1 admission /
call-composition failure. Location coverage and the individual C5 spatial
proof do not repair an absent query.

The selected run-2 repair now accepts same-head STAR for precise STAR
demand, for FLOW and concrete FULL marks, with their existing layer and
companion rules. C5 uses the same revised raw image. Exact demand and later
run admission are unchanged. The linked repair has the new proof and native
results; the search counts below describe the earlier, unchanged sweep.

## 2. Bounded reference search

Two executable scripts extend the earlier conditional-marking helper family:

- [Search.lean](data/bidirectional-experiment-sources-20261118/scripts/demand_experiments/soundness-followup-20261117/Search.lean): 504 configurations.
- [NegativeSearch.lean](data/bidirectional-experiment-sources-20261118/scripts/demand_experiments/soundness-followup-20261117/NegativeSearch.lean): 280 configurations.

The helpers have two positive marking actions, one with a field-dependent
condition and one with a whole-input condition. The caller reads h from
each helper result. Parameters include source/guard paths up to four fields,
EXACT/MUST marks, exact or uniform output, mark changes, and one to four
calls. Some inputs carry real E or inherited H as explicit packet controls;
they are not claimed to be unconditional marking-rule outputs in run-1.

| Sweep | Configurations | Concrete observation exists | No concrete observation | Natural stop range | Latest diagnostic |
|---|---:|---:|---:|---|---|
| Original output region | 504 | 504 | 0 | run-3 to run-13 | run-25 |
| Alternative output region | 280 | 93 | 187 | run-3 to run-9 | run-25 |
| Total | **784** | **597** | **187** | run-3 to run-13 | run-25 |

The 504 cases contain 336 inputs with Empty E/plain H and 168 E/H controls.
The 280 cases contain 187 Empty E/plain H inputs and 93 controls. There are
523 base cases and 261 controls in total. The search uses the selected C2,
qualified rows, native-bound delivery selector and uniform packet coverage.
Each round is checked against another round for a within-run fixed point.
All 784 final observations match the concrete reference; all checked rounds
are fixed points. No sampled case had an unclosed frontier at run-25.

| Natural stop | First sweep | Alternative sweep |
|---|---:|---:|
| run-3 | 37 | 166 |
| run-5 | 125 | 71 |
| run-7 | 192 | 36 |
| run-9 | 114 | 7 |
| run-11 | 28 | 0 |
| run-13 | 8 | 0 |

These are finite executable observations, not a universal soundness proof
or a proof of all later rounds. The search's helper grammar does not include
an ordinary strong field overwrite with a STAR-to-STAR DEMAND summary. It
therefore did not exercise the new counterexample's missing cell. The
separate native/model example supplies that coverage.

## 3. Other checks and rejected candidates

The filter-normalization candidate is already an accepted precision gap:
[interpreter.md §5.1](../../spec/interpreter.md#51-type-filter-filterbase-may)
keeps unknown tails and does not carry the path filter in a summary. Its
exactness claim is restricted to valid locations (I13). Mark-policy losses
are also a declared G6 boundary. No new violation is claimed from these
already excluded cases, and no type-policy semantics were changed.

A retained NORMAL parent-MUST summary can reject a child-MUST actual under
the selected definite matching rule. That legal interface countermodel is
already in the audit. The present work has not established a new cold
program failure from it; it remains a proof obligation about future guidance.

The new wrapper/overwrite case is different: the exact current offer is
constructed by an admitted query, and the only rejected cell is witnessed
by a controlled cold native run. No later-run data, type guess or cutoff
is used to label that rejection unsafe.

## 4. Proof and native evidence

The [new proof package](../../spec/lean/proposals/nested-star-admission-gap-20261117/README.md)
adds 16 constructive claims: **7,124 cumulative across 410 checked modules**.
It computes the selected C2/C5 trace, both run-1 return and mutable-argument
rows, the true untouched g point, the missing NORMAL record, and the empty
future call service. Only `propext` and `Quot.sound` are permitted in the
transitive axiom closure. The focused control model is not a formal model
of the entire native driver.

The original three native tests covered four cold scenarios:

| Scenario | NORMAL observations | Latest natural run |
|---|---:|---|
| Current policy, nested overwrite | 1 | run-3 |
| Selected rejection adapter, nested overwrite | **0; no provisional result** | run-3 |
| Direct overwrite call | 1 | run-3 |
| Nested call without overwrite | 1 | run-1 |

The adapter keeps replay, ZERO, native write/normalization, C5 and the driver.
It rejects only the old emitter's checked inner root EXACT/FLOW start for
the captured same-head STAR/FLOW offer. It is a test of the specified cell,
not an installed version of the entire proposal. The test asserts the broken
result as a diagnostic; it is not evidence that this C2 rule is correct.

The run-2 relay delta now repairs that concrete case and adds two native
tests: the NORMAL g observation and overwritten-f negative, both at natural
run-3 completion. The latest combined targeted suite passes 65 tests. Its
36 new constructive claims bring the audited chain to 7,160 claims in 412
modules. General native correspondence, cross-iteration relevance, complete
FLOW lifting and loop-handoff proofs remain open. See the selected delta
for the updated scope and reproduction command.

Compiled modules, full captures, source hashes, XML and receipts stay outside
Git under `report-data-archive/.../data/soundness-followup-20261117/`.
