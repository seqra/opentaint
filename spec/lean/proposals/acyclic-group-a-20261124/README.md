# Group A rules of the acyclic proposal: Lean models

24 November 2026. Lean **4.36.0**, core library only. Production is not
changed by these files. Proposal:
[acyclic-group-a-implementation.md](../../../acyclic-group-a-implementation.md).
Follow [proof-guide.md](../../../proof-guide.md).

| Module | Claims | Contract |
| --- | ---: | --- |
| `G6DropForm.lean` | 15 | R1, the G6 drop form: it extends native; it is native without a boxed level and for primitive-tracking marks; region exactness, prefix closure (ap.md S5) and monotonicity in K; the M4 counterexample for native; the conjunction of two policies; the production accumulation and the reference compute the same predicate |
| `MustExactCleaner.lean` | 12 | R2, an EXACT cleaner on a MUST leaf: native demotes the leaf, R2 keeps it; the only change is the layer of one row; equal positions; the tree position equals the reference position; no finite NORMAL form of "the region without the point" (executable witness); the OWASP `Thing2` reduction |

Every claim is constructive. The audited axioms are `propext` and
`Quot.sound` only: no `Classical.choice`, no `sorry`, no custom axiom, no
`native_decide`. Both files declare a local constructive `LawfulBEq Nat`
instance, because the library instance depends on `Classical.choice`.

## Reproduce

```bash
spec/lean/proposals/acyclic-group-a-20261124/check.sh
```

It compiles both files with `elan run leanprover/lean4:v4.36.0 lean` and
fails on an error, a `sorry` or an axiom outside `{propext, Quot.sound}`.

## Scope

The models are local to one operation: one mark, one leaf or one path.
They do not prove whole-analyzer soundness or termination. The
assumptions A1-A3 of the proposal (§3.4) are code readings. The existing
`ApSpec` cleaner model (`AnyTaintExDefs.partX`) still describes the
native cleaner.
