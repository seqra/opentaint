# Proof index for demand refinement and termination

The [specification](../../../demand-refinement-and-termination.md) contains
the full selected contract and local proof arguments. This index identifies
the executable witnesses and theorem sources. Earlier proof packages
retain their stated assumptions and activation scopes. The later
[comparative audit](../../../demand-refinement-no-loss-audit.md) adds
source-control guards and the native handoff exceptions.

| Rules | Constructive proof sources |
| --- | --- |
| R01–R03 | [Field semantics](../termination-soundness-audit-20261117/AuditGeometry.lean) and [scalar cut coverage](../termination-soundness-audit-20261117/AuditIntersection.lean). Every truncated point keeps a nonempty removed suffix. |
| R04–R06 | [C2](../non-empty-may-20261113/Policy.lean) and [bounded binding](../bounded-refinement-frontier-20261114/README.md). Legal raw starts, NE inclusion in MAY, and possible-binding support. FLOW companion proof uses R22. |
| R07/R08 | [Same-head holes](../concrete-query-exclusions-20261116/CarrySafety.lean) and [deeper-head safety](../excluded-head-admission-20261116/HeadSafety.lean). Exact geometry preservation and exhaustive cap exception. |
| R09–R12/R23 | [Bounded plans and qualified union](../bounded-refinement-frontier-20261114/README.md), [child cover](../prepared-child-saved-replay-20261115/ChildCover.lean) and [real exclusions](../exclusion-child-replay-20261115/README.md). A covered field contribution retains its full paired output service. |
| R13 | [Point writes](../point-write-progress-20261115/PointWriteProperties.lean). A strict-descendant keep cannot use an exact root. |
| R14 | [Saved-first call model](../bounded-refinement-frontier-20261114/README.md) and [saved replay](../prepared-child-saved-replay-20261115/README.md). Original actual and old saved service survive empty current admission. |
| R15/R16 | [Strict MUST saved replay](../definite-must-replay-20261116/README.md) and [definite replies](../definite-reply-support-20261116/README.md). Definite geometry, preservation of previous NORMAL results and equal-key support. |
| R17 | [Uniform actual coverage](../normal-must-actual-coverage-20261116/README.md) and the [positive continuation theorem](../termination-soundness-audit-20261117/AuditGeometry.lean). |
| R18/R24 | [Retained provider and uniform NE coverage](../normal-uniform-ne-coverage-20261114/README.md) and [concrete/protected same-lane extension](../same-lane-uniform-termination-20261114/UniformService.lean). |
| R19 | [Owned closure](../complete-point-service-20261116/CompleteClosure.lean), [mark scope](../mark-scoped-point-service-20261116/README.md), [reply scope](../reply-scoped-point-service-20261116/README.md), [layer](../layer-aware-point-service-20261116/README.md), [same H](../flag-aware-reply-service-20261117/README.md) and [native bound service](../native-bound-reply-service-20261117/BoundCoreProof.lean). Whole committed coverage for all relevant returns. |
| R20–R22 | [Raw witnesses](../termination-soundness-audit-20261117/AuditServices.lean), [exit selection](../termination-soundness-audit-20261117/AuditIntersection.lean) and [NORMAL suffix lifting](../termination-soundness-audit-20261117/AuditNormalization.lean). |
| R25/R27–R30 | [Positive kernel](../termination-soundness-audit-20261117/AuditKernel.lean) and [complete context](../termination-soundness-audit-20261117/AuditScopedService.lean). Transitive final storage, least-result order, monotone effects and whole ND derivations. |
| R26/R35/R36 | [Selected cleaner policy](../uniform-root-cleaner-cycle-20261114/RootCleanerPolicy.lean) and [uniform residual](../uniform-cleaner-spine-20261117/UniformCleanerSpine.lean). Explicit EXACT coarsening, exact subtree subtraction, and cold repaired traces. |
| R31 | [Disjoint cleaner transfer](../disjoint-cleaner-flow-20261117/DisjointCleaner.lean) and [getter trace](../disjoint-cleaner-flow-20261117/CleanerRepairTrace.lean). The prefix guard protects the complete normalized suffix region. |
| R32/R33 | [Run-2 relay](../run2-star-relay-20261117/README.md) and [handoff masks](../handoff-mask-audit-20261117/MaskHandoff.lean). Old cells remain, and the new raw family and F72 keep their own-row service. |
| R34 | [Possible DIRECT replay](../saved-direct-possible-replay-20261117/README.md). Preserves successful old reads and D-only new support. Cold repair resumes the missed route. |
| R37/R38 | [Terminal lineage](../recursive-target-service-20261117/TargetSupport.lean) with [source-specific witnesses](../mark-origin-soundness-20261117/OriginService.lean). The lineage theorem alone does not authorize report-ID-only retirement. |
| R39/R40 | [Regular emptiness and branch recurrence](../branching-field-cycle-20261117/README.md) and [nested state pairs and cold search](../two-sided-field-cycle-20261117/README.md). Closure excludes every complete shared word. Extraction and whole native service have separate obligations. |

[CondensedDemandRefinement.lean](CondensedDemandRefinement.lean) proves
seven composition checks. It checks transitive service for complete
positive derivations, distinguishes raw initials that share a public
key, exercises the paired limit and row isolation, and combines terminal
lineage with mixed per-origin NORMAL and absence certificates. It reuses
the checked quiet suffix for the nested example.

Use Lean 4.35.0 with the R40 receipt in the external data root. The checker
verifies all 448 parent source hashes, compiles the new module and audits
each transitive axiom set. The allowed axioms are `propext` and `Quot.sound`.

```sh
python3 spec/lean/proposals/demand-refinement-spec-20261117/check.py \
  --dependencies /absolute/external-data/two-sided-field-cycle-20261117/checked-proofs \
  --out /absolute/external-data/demand-refinement-spec-20261117/checked-proofs
```

The receipt has 7 new claims and 7,501 cumulative claims in 449 modules.
The latest native campaign had 179 passing tests. Its adapters, reference
comparisons and expected baseline misses retain their stated scopes.
