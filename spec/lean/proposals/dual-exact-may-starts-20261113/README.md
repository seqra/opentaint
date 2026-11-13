# Dual EXACT/FLOW and MAY starts

Local investigation for the [candidate report](../../../../docs/reports/bidirectional-dual-exact-may-starts-20261113.md).
No new analyzer policy is installed.

```sh
lean spec/lean/proposals/dual-exact-may-starts-20261113/DualStarts.lean
```

Lean 4.35.0 checks eleven constructive declarations. The axiom audit has no
`Classical.choice`, `sorryAx` or custom axiom; some statements use `propext`.
The model is executable, with finite paths and literal copy/read witnesses.

Checked scope:

- Two distinct FLOW initial keys: exact NORMAL and MAY DEMAND.
- Neither initial nor live start conclusion has STAR. STAR is introduced
  by the modeled summary normalization, not by these start commands.
- Exact copy normalization to a correlated NORMAL STAR relation.
- Equal application results for STAR-to-STAR NORMAL and MAY-to-MAY DEMAND
  on a **same-head MAY** input. The result stays MAY/DEMAND.
- The corresponding relation-inclusion claim on arbitrary concrete path
  pairs is false: MAY can change a suffix; STAR preserves it.
- A forward field read can have only the MAY result; its exact root probe
  cannot supply that read.
- A backward exact returned point can infer the NORMAL getter relation.
- Extending the application-equality claim to a deeper MAY input changes
  its result geometry and needs another proof.
- The historical STAR read still creates MAY as an operator fact. Its
  STAR input is outside the clarified new start domain and is not a
  counterexample to that policy. The new two-start read has one absent
  result and one MAY result; it has no STAR-origin result.

This is not a proof of full C2/C5, exclusions, mark changes, ND, literal
protection, ports, persistence, handoff demand removal or eventual findings.
In particular, equal results for one input class do not alone prove that
deleting its next-run demand preserves future refinement opportunities.
Six source-built native AP tests check the corresponding operator cells;
the new emission and storage policy is not implemented by those tests.
