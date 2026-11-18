# Uniform reply survives exact support absorption

Follow [proof-guide.md](../../../proof-guide.md).
[Code and complete annotated trace](../../../../docs/reports/bidirectional-provisional-uniform-nontermination-20261116.md).
Production is unchanged. Latest native capture: **run-31**, policy ceiling.

The conditional producer tests `CM(p.MAY,T)` and assigns U uniformly at a
fresh local r. Ordinary return transfers r to ret. Two actual inputs supply
NORMAL T uniformly at p and only at p.f. There is no loop, recursion,
cleaner, pass rule, alias, static field or unresolved body.

The latest policy's cold prefix is computed, not supplied as saved summaries:

```text
run-3: infer p.MUST/T   -> ret.$/U,N and ret.MUST/U,N
run-5: infer p.f.MUST/T -> ret.$/U,N and ret.MUST/U,N
```

For a NORMAL p.f.MUST/T offer, saved replay has both definite and provisional
results. The selected exact FULL reply filter is **enabled**. It removes
the provisional ret.$/U copy but keeps ret.MUST/U,D. The uniform NORMAL reply
does not remove that support under the current contract.

`UniformCycle.lean` checks **30 constructive claims**:

- Complete cold states through run-6: selected C2 families and companions,
  each candidate's paired raw C5, exit selection, normalization, cuts,
  ordinary producer/return, NORMAL record retention, original caller
  offers, typed Targets and source permissions.
- All four scalar NORMAL members, including the extra exact outputs added
  by the latest empty/nonempty initial-emission policy.
- The exact filter runs and leaves the uniform DEMAND member. That member
  survives arbitrary extra ready results and reversed record enumeration.
- Native concrete MUST definite/provisional and reverse-view cells.
- `history(n+6) = stateAfterRun6` for every natural n. Both findings are
  NORMAL, make demand is empty, and root DemandTarget remains nonempty.
- No completed run reaches the empty continuation. The proof has no ceiling.

The previous exact-output counterexample and its run-7 repair are unchanged
dependencies. This example changes the ordinary producer's assignment tail
and the observation pattern; it does not disable that repair.

```bash
python3 spec/lean/proposals/provisional-uniform-cycle-20261116/check.py \
  --out /tmp/provisional-uniform-proofs
```

`--dependencies DIR` can reuse the exact-support proof build after checking
every source hash. The new module and every new theorem's axiom closure are
compiled/audited again. Only `propext` and `Quot.sound` are allowed. There
are no custom assumptions, classical choice, holes or external proof oracle.
The receipt covers **2,210 declarations in 110 modules**, including reused
source-hash-checked dependencies. Generated files remain outside the repo.

Scope is the fully analyzed synthetic unary producer/observation cone with
two real call inputs. Ordinary untouched identities and ZERO completion add
no U and are outside the returned cone. The native fixture runs the real
actor/driver through run-31 and checks the reused matching and reverse-view
cells. Its component adapter also checks complete native packet folding and
the latest exact filter. The native core has not installed the whole NE/C2
proposal; its cold trace has two uniform NORMAL members, while the latest
formal trace also has the two exact members. Both traces keep the same
uniform DEMAND witness. No whole-engine or Java-front-end simulation is
claimed. No production repair is selected by this counterexample.
