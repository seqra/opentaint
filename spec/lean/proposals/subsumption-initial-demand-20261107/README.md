# Subsumption, initial emission and demand intersection proofs

7 November 2026. This package checks the declared component domains and the
scoped principal routes for the [combined specification](../../../edge-subsumption-initial-emission-demand-intersection.md).
Read the [examples E01–E28](../../../subsumption-principal-examples-20261107.md)
and [proof map P01–P23](../../../subsumption-initial-demand-proof-obligations.md).
No runtime implementation or project measurement is included.

## Repeat the check

[manifest.json](manifest.json) pins every model and its baseline imports.
The checker first builds the imported AP library, then compiles the models
and prints every declared theorem's axiom dependencies. It rejects proof
holes, custom axioms, classical choice and changed source pins. Only
`propext` and `Quot.sound` may occur in the printed axiom lists.

From the repository root, choose a new output directory:

```sh
python3 spec/lean/proposals/subsumption-initial-demand-20261107/check.py \
  --output-directory /tmp/subsumption-initial-demand-check
```

The final root check passed with **684 declared laws**, including the 162
reused original laws and the negative interface checks. Read the
[receipt](component-checks-684.json) and [complete axiom audit](component-axioms-684.log).
Earlier 126, 308, 471, 619, 627 and 640-law receipts remain as historical
evidence. A count includes negative and representation laws;
it is not a count of whole-analyzer soundness theorems.

## Models and limits

| Model | Laws | Checked domain |
| --- | ---: | --- |
| [Canonical](Canonical.lean), [Relations](Relations.lean), [Matching](Matching.lean), [Reachability](Reachability.lean) | 162 | Byte-identical original 528 sources. Compatible MAY/MUST/E laws, aligned relation suffixes, native-role filter and finite relation paths. Original protected-prefix removal is superseded by literal H. |
| [RelativeAdmission](RelativeAdmission.lean) | 47 | Arbitrary Nat field paths/full marks, finite E, restricted FULL C2 and constructive normalized C5 image; 24 executable cells |
| [ExactFlowInputBridge](ExactFlowInputBridge.lean) | 30 | Existing legal EXACT/FLOW actuals with nonempty E; query-local erasure only, original actual preserved |
| [AnnotatedC5Exit](AnnotatedC5Exit.lean) | 57 | Typed counted accessors, mark/E/H/support-preserving exit selection, complete ND P, complete row union and DEMAND cuts; entry image is a callback |
| [LiteralProtection](LiteralProtection.lean) | 19 | Literal typed H, freshness, arrival orders and pass transport; unchanged DATA operation is a parameter |
| [SelectedTransitiveSubsumption](SelectedTransitiveSubsumption.lean) | 38 | A→B→C without stored B, equal-mx aligned guards, T exclusions/H, local marked work and both arrival orders |
| [FlowDemandCompletion](FlowDemandCompletion.lean) | 50 | Final-source provenance, both DATA endpoints, legal static prefixes, one paired erasure, exact interfaces and linear row-count bound |
| [WrapperRecovery](WrapperRecovery.lean) | 34 | Real loop-free source/read/call/permission/finding bootstrap at 1,1,2 for arbitrary finite ordinary wrapper chains |
| [ConcreteConverterWrapper](ConcreteConverterWrapper.lean) | 17 | E18 actual guarded T→U source kernels, C2/C5 publication, finite wrappers and wrong-mark controls; source occurrence callback is an adapter obligation |
| [StaticFlowCompletion](StaticFlowCompletion.lean) | 20 | Actual E19 C2/body/C5 NORMAL provider; same-field kill, exact-parent and E28 paired cross-base controls |
| [TwoLoopHeaderFlow](TwoLoopHeaderFlow.lean) | 27 | E20 header10→4 versus repeat4→4, real source permission/getter/sink path, weak fixture and strong negative |
| [OwaspUniformCompletion](OwaspUniformCompletion.lean) | 24 | Arbitrary H-depth uniform source/body, paired C5 no-cut invariant, real FLOW backing and plain-T arm removal |
| [DeepFlowCompletion](DeepFlowCompletion.lean) | 35 | Supplied whole completed query, fine-versus-cut distinction, derived NORMAL shrinker and finite source/read/sink chain |
| [DeepGuidanceArrival](DeepGuidanceArrival.lean) | 35 | Actual F1/B2/F3/B4 source/Target/ZERO arrival and physical ports under global limits 1,1,2,3,4 |
| [GeneralLoopAdmissionBound](GeneralLoopAdmissionBound.lean) | 19 | ALL labelled query families under a head bound; canonical E07 root MUST finding in both orders |
| [GeneralLoopAdmissionOneStep](GeneralLoopAdmissionOneStep.lean) | 8 | Every C2/public key has depth≤demand depth+1 independently of actual depth; B4 global3 actual-depth3 cell |
| [LoopMapperRecovery](LoopMapperRecovery.lean) | 13 | E16 actual loop-write result, B2-derived adjacent demand, ALL extra-family cut distinction and NORMAL mapper/sink pipeline |
| [DeepExtraFrontier](DeepExtraFrontier.lean) | 27 | F3 cap/read producer grammar, independent B4 initial/output bounds, ALL additional F5 families and actual F5 limit4 cut distinction |
| [StaticCarryGap](StaticCarryGap.lean) | 22 | Old no-FLOW-route counterexample and conditional-pass anti-promotion control |

`Discovery`, `LoopGeometry` and `ExceptionalControlDemand` are pinned existing
control helpers for the arrival model. `LoopGeometry` is a module-name alias
for the old loop helper. It is distinct from the C5 `Geometry` helper. No
helper theorem is counted again as a new feature result.

`DeepFlowCompletion` has local backward re-entry cells at `(run=4,limit=2)`.
That is not the native run-4 global limit. `DeepGuidanceArrival` uses the
actual run-4 global limit 3 and pair-relative caps. `DeepExtraFrontier` connects ALL relevant family heads within the source,
cap/read and nonexpanding read-replay grammar. It proves the fine F5 key is
not masked by any additional bounded query family. Native producer/store
coverage and final-basis preservation remain explicit adapter obligations;
a supplied recorded row list is not assumed exhaustive.

The OWASP component proves the stated uniform producer family, not arbitrary
Java. In the principal 1,1,2 schedule, every reversed B2 DATA entry has depth
at most 1, so its paired bound n≤s+1 holds for every original row. Self-pairs
have n=s; paired erasure preserves n,s. Native packet/delta and driver
correspondence remain explicit implementation checks.

## Negative evidence and unchanged source semantics

`StaticCarryGap` deliberately keeps its no-other-DATA-provider assumption.
The old interface then has no run-3 DATA output despite source permission
and saved ZERO replay. The new demand completion refutes that assumption
by enabling ordinary analysis to infer a real NORMAL FLOW provider. It does
not change later precise-STAR rejection or promote a concrete DEMAND row.
The conditional-pass control also proves why STAR shape and H=false do not
justify such promotion.

[SourceTransferAudit.md](SourceTransferAudit.md) and its source pins record
the unchanged compiler/gates. A surviving positive source guard needs its
concrete mark. Baseline negative-condition projection can make a ZERO source;
it does not turn a FLOW hypothesis into concrete evidence. No new source
permission or grounding label is introduced.

## Evidence boundary

The receipt uses `PASS_LOCAL_COMPONENTS_ONLY`, `nativeAnalyzerProved=false`
and `allPrincipalProgramsProved=false`. There is no single formal theorem
for all native programs. Component proofs, scoped producer/consumer proofs,
source audits and historical native traces are distinct evidence.

Native Kotlin/store correspondence, the exhaustive native producer adapter,
GROUP's known issues, arbitrary aliases/ND and whole-driver convergence are
not proved here. They are implementation gates in the specification. Keep
strict principal assertions and natural stopping when implementing. Latest
historical static captures completed run-3; the Deep capture completed run-5.
No new native redesign result is claimed.
