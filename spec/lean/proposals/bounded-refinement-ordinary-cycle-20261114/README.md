# Ordinary-code uncapped counterexample

[Code, annotations and non-termination proof](../../../../docs/reports/bidirectional-bounded-refinement-ordinary-cycle-20261114.md).
No pass rule, loop, recursion, alias, static, cleaner, ND rule or predefined
summary. Production is unchanged.

The helper either reads two f fields or wraps its input under two f fields.
The caller invokes it twice. A standard whole-object source gives NORMAL
MUST; a standard whole-object sink has a backward MAY seed.

At forward limit L, an initial at L-1 grows past the global limit. It
becomes NE/DEMAND before NORMAL precoverage. Call 2 admits the at-limit
STAR initial. The backward dual regenerates the next forward row at L+1.
The helper heads grow indefinitely; the root's ZERO -> DemandTarget edge
repeats unchanged in every round.

`OrdinaryCycle.lean` imports the selected `Policy`/`Restriction` and current
`LocalRouting` proposal. All initial offers are supplied by real sources,
sink seeds or the preceding call result. The bootstrap is computed from
run-1/run-2. The induction has no iteration limit and retains existing
NORMAL provider behavior. Arbitrary local masks cannot prune a known
prefix write, and arbitrary NORMAL coverage cannot precover a D cut.

```sh
python3 spec/lean/proposals/bounded-refinement-ordinary-cycle-20261114/check.py \
  --out /tmp/bounded-refinement-ordinary-cycle-proof
```

The checker verifies every theorem's axiom closure. It rejects compiler
warnings, proof holes, custom axioms and classical dependencies; only
`propext` and `Quot.sound` are permitted. Sources and logs are hashed in
an external receipt.

Checked: **13 modules, 241 audited declarations**: 42 new theorems and
199 imported proposal/reference claims. Receipt:
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/bounded-refinement-ordinary-cycle-20261114/proofs-v2/receipt.json`.

Scope: constructive prefix/action/control witness, with the full-spec
embedding and compaction-survival argument in the report. Not a native
new-tail execution or full JVM/scheduler equivalence proof. The report's
exploratory run-31 result is not the basis of the infinite claim.
