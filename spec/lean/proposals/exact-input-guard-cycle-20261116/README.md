# Exact-input guard recurrence

16 November 2026. Follow [proof-guide.md](../../../proof-guide.md).
[Code, explanation and uncapped proof](../../../../docs/reports/bidirectional-exact-input-guard-nontermination-20261116.md).
[Complete per-block run trace](../../../../docs/reports/bidirectional-exact-input-guard-trace-20261116.md).
Production is unchanged.

An exact entry assignment at a.f.g.$ replaces the previous MUST/overwrite
program. There is no field write, loop, recursion, cleaner, pass rule,
unresolved body or intrinsic-MAY action. All three acyclic calls use the
same fully analyzed make owner and four ordinary literal marking rules.
The current NORMAL-MUST/real-E cap exception is imported unchanged.

## Checked result

**166 new constructive claims; 5,160 audited declarations in 259 modules**,
Lean 4.35.0. Only `propext` and `Quot.sound` are allowed in theorem axiom
closures. No custom axiom, hole, classical choice or external evaluation
oracle is used. Frozen values are executable witnesses checked by the kernel.

```text
forall n >= 0:
    history(9+2n) = frozenForward
    history(10+2n) = frozenBackward

forward.rows.length = 70; backward.rows.length = 82
forward.saved = backward.saved; length = 10
forward.report = true
forward.observationActive = true
backward.sourceAllowed = true
```

Concrete repeated rows are `[ret.M/flip(m) | p.*/m]` after every later
forward run and `[p.M/m | ret.*/flip(m)]` after every later backward run,
for both m=T and m=U. No later forward stop succeeds. The cold prefix skips
no earlier natural stop. Every within-run result is quiescent. Steady
transitions and fixed points hold for **every budget n+8**, then follow the
uncapped `1,1,2,3,...` schedule.

The complete cold prefix and every later state have **Empty E throughout**.
Generic C2 legality proves that later offers obey the ordinary global and
Dc+1 input bounds. No input-cap exception is invoked. Paired output cuts
remain unchanged. Accumulated Targets include every intermediate delivery;
NORMAL observations never cancel them.
The complete prepared families, including child queries, are also checked
against their own row's two input bounds for every steady budget n+8.

## Modules

| Module | Proof scope |
|---|---|
| ExactGuard | Same current marked-return/control machine, with an exact entry assignment and no overwrite |
| ExactPhase | Direction/budget phase equivalence through current CarryPolicy and HeadPolicy gates |
| ExactFrozen | Complete forward/backward witness states |
| ExactRounds | Arbitrary-budget pure delivery/publication equalities and eight sweep transitions |
| ExactCold | Cold run-1..run-10, reached states and within-run fixed points |
| ExactKernel | Coarse first-field admission, fine exact rejection of deep guard, valid h result, actual summary application, failed child coverage, reverse request, cap-ineligibility and ordinary input bounds |
| ExactSteady | Arbitrary-budget steady transitions, accumulated Target and every later scheduled run |
| ExactRecurrence | Uncapped two-state induction, concrete repeated row witnesses, no stop, sizes, complete Empty-E state invariant, ordinary entry caps for later domains and complete prepared-family bounds |

These are proofs of the stated reference scope, not a full JVM/IR or
whole-production equivalence theorem. Native component controls check the
decisive transfers and application. The native full control retains its
explicit report-count difference from the proposed reference.

## Reproduction

```bash
python3 spec/lean/proposals/exact-input-guard-cycle-20261116/check.py \
  --out /tmp/exact-input-guard-proofs
```

The default checks all dependencies. Reuse a previously checked current
policy output with source hashes verified first:

```bash
python3 spec/lean/proposals/exact-input-guard-cycle-20261116/check.py \
  --dependencies /drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/excluded-head-admission-20261116/proofs-restricted-final \
  --out /tmp/exact-input-guard-proofs
```

Current receipt:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/exact-input-guard-cycle-20261116/proofs-final/receipt.json
```

The sibling `scripts/demand_experiments/exact-input-guard-cycle-20261116`
contains the finite exporter, pure-stage exporter and trace renderer.
Set LEAN_PATH to a checked output, run `lean` on the selected exporter,
and redirect output outside the repository. The renderer never provides a
proof oracle. Encoding: base 0=p, 1=ret; fields 1=f, 2=g, 3=h; marks 1=T,
2=U. The finite reference capture reaches **run-31**; the proof is uncapped.

The new native full/component tests plus current admission controls give
**22 passing tests**. The unchanged driver reaches **run-31/POLICY**, NORMAL
report count 0, with a root DemandTarget in every run. The proposed reference
has a NORMAL observation from **run-3**. The report gives commands and limits.
