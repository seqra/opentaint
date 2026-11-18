# Source-specific Target service proof package

**R38 [REC] [LOOP]**, 17 November 2026. Production is unchanged.
[Paired traces, rule, costs and scopes](../../../../docs/reports/bidirectional-mark-origin-service-soundness-20261117.md).
[Current consolidated proposal](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md).

R37's report-ID certificate does not preserve every marking-point/full-mark/
observer relation. Two distinct marking points can share one full T and
observer ID. The native baseline reaches the deeper point at **run-5**;
the report-only handoff adapter naturally stops at **run-3** without it.
R38 closes a goal only when every possible origin has a valid NORMAL route.

## Proof inventory

| Module | New claims | Checked contract |
| --- | ---: | --- |
| `LostMarkOrigin` | 12 | Ordinary three-read NE cuts; cold forward run-1/3/5 and backward permissions; natural run-3 loss; no recovery at any later pair; equal report IDs do not prove relation equality |
| `OriginService` | 16 | Constructive finite path closure; source-specific upper/lower service; unknown fallback; extra NORMAL paths; recursive cycles; normal activation versus route; queue/list membership equivalence |
| `OriginGrowth` | 2 | NORMAL root generation followed by four real write cuts still needs the deeper run-5 observed route |
| `OriginRepair` | 11 | Corrected cold history, baseline deep relation, uncapped quiet suffix; unique-origin fast path; earlier natural run-7 recursive result; two-origin recursive control through natural run-9 |
| `OriginSearch` | 2 | Exact source comparison and executable fresh 7,686-configuration sweep |

**43 new constructive claims; 7,403 cumulative in 436 source-hash-pinned
modules.** Lean **4.35.0** checks every new claim. Transitive axiom inspection
allows only `propext` and `Quot.sound`. There are no proof holes, custom
axioms, classical choice or external decision shortcuts.

The path theorem explicitly takes the adapter's complete marking catalogue,
future-route-to-upper map and NORMAL-path-to-valid-witness map. It does not
assume that an arbitrary native graph already supplies those maps. The
supported flat and pure-neutral-wrapper references supply concrete witnesses.
No source vector is propagated on DATA. Normal report count is not the
soundness oracle. Old R37 proofs remain historical dependencies with their
original narrower terminal-ID statement.

## Reproduce

Use the previous source-checked receipt as the parent and a fresh output
directory outside Git. Under the external data root, the supplied parent
is `recursive-target-service-20261117/checked-proofs/`.

```sh
python3 spec/lean/proposals/mark-origin-soundness-20261117/check.py \
  --dependencies /absolute/external-data/recursive-target-service-20261117/checked-proofs \
  --out /absolute/external-data/mark-origin-soundness-20261117/checked-proofs
```

The checker verifies all 431 parent source hashes, compiles the five new
modules, inspects every claim's transitive axioms, and runs the fresh sweep.
The exact expected output is:

```text
ORIGINS flat=6615 loops=735 recursive=336 failed=0 latestNaturalRun=9
```

The 6,615 flat word configurations compare each exact marking relation,
not one report Boolean. The 735 loop components check finite ordinary
repeat closure and a broad AL observer. They do not model hierarchical
native ports. The 336 direct/mutual recursive cases settle shared summaries
for two marking offers, then use read-only pure NORMAL FLOW witness queries.
Every checked within-run closure is fixed and every listed refinement ends.
The finite loop/reference search bound is not an uncapped convergence proof.
The separate concrete loss/fixed-history theorems quantify all later pairs.

## Native checks

The baseline is `966a40c3647268cc006e5776591d6b68849379d0`.
FULL mode and the uncapped test `IncreasingLimits` use **1,1,2,3,...**.
The diagnostic recursive control alone uses its named run-15 policy cutoff.

```sh
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.DistinctMarkOriginServiceTest \
  --tests org.opentaint.dataflow.bidi.LoopMarkOriginServiceTest \
  --tests org.opentaint.dataflow.bidi.OriginServiceCertificateTest \
  --tests org.opentaint.dataflow.bidi.RecursiveWrapperTerminationTest --offline
```

The combined earlier 123-test suite plus **20 new tests** passes **143 tests**
in 22 classes. Expected-broken proposal/native controls assert the documented
loss, not a successful repair. The flat adapters change only completed root
Target handoff. They call the native barrier first and leave DATA records,
source permissions, transfer, C2/C5 and all caps intact. Native traces still
contain the pre-filter DT row; the adapter then returns natural NO_DEMAND
only because that root row was its sole remaining guidance. It is not a
policy timeout. R38 declines that deletion until both distinct origin
witnesses are proved.

The recursive adapter reconstructs only the next root Target handoff,
keeping DATA demand, saved records and seeds. The source-specific variant
uses each native NORMAL output suffix as a proof witness for these explicit
pure wrappers; it is not a generic arbitrary-source tracer.

| Native case | Latest completion |
| --- | --- |
| Flat baseline and R38 | natural run-5; distinct deep NORMAL fact present |
| Flat report-only R37 control | natural run-3; deep relation absent |
| NORMAL source followed by field writes | Same run-5 versus run-3 difference |
| One actual hierarchical loop, baseline/R38 | natural run-13; deep relation present |
| Two nested actual loops, baseline/R38 | natural run-17; deep relation present |
| Either loop report-only R37 control | natural run-5; deep relation absent |
| Single-origin recursive repair | natural run-7, unchanged |
| Two-origin recursive repair | natural run-9; both origins served |
| Unchanged recursive diagnostics | run-15/POLICY, not natural convergence |

## Limits

The package does not prove whole-analyzer termination or soundness. G1–G4
and general upper/lower witness adapters remain open. The fresh scope has
one shared full T and one unary observer. General ND, mark changes, aliases,
statics, GROUP and cleaner/recursion mixtures are not certified by this
query adapter. Unknown keeps guidance. A coarse possible-origin view can
also keep guidance indefinitely; the selected rule is not a universal
termination theorem. Do not infer impossibility from an unexecuted generator
or from a finite current-state dump.

The actual native loop controls check ports/C2/C5 through run-17; their
counts are separate from the simple loop-component reference. Older cleaner
and ordinary controls remain in the cumulative proof/native validation.
All compiled objects, receipts, logs, XML and detailed captures are outside
Git under `mark-origin-soundness-20261117/` in the
[external data root](../../../../docs/reports/EXTERNAL_DATA.md).
