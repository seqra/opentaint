# Direct provisional MUST replay: uncapped cycle

Follow [proof-guide.md](../../../proof-guide.md).
[Code, annotated trace and native evidence](../../../../docs/reports/bidirectional-provisional-must-nontermination-20261115.md).
Production is unchanged. Latest native capture: **run-31**, policy ceiling.

Two ordinary NORMAL marking inputs supply T at p and at p.f. A conditional
producer tests `CM(p.MAY,T)` and assigns U exactly at a fresh local r. The
method returns r. Two calls infer NORMAL native records:

```text
p.MUST/T   -> ret.$/U,N
p.f.MUST/T -> ret.$/U,N
```

Direct saved replay of the first record on the second input uses its existing
provisional lane. It creates an EXACT U result on DEMAND. The second record
also gives a NORMAL result. The support layers remain separate.

`Cycle.lean` reuses the selected `Policy.emit`, raw `restrictOne`, paired
output intersection, normalization, cuts and typed Target kernel. The added
native-record functions represent the definite/provisional concrete MUST
split and the existing reverse-MUST/exact read. Native component tests check
those functions' relevant cells separately.

**30 constructive theorems** check:

- The complete cold producer/observation-cone states through run-6, including
  actual inputs, query layers, admitted source relations, saved reads,
  producer permissions and NORMAL report IDs.
- Definite and provisional reads, layer-separated complete replies, no fresh
  helper query with empty demand, and the valid root Target/ZERO C5 pair.
- Induction: `history(n+6) = stateAfterRun6` for every natural n. In each
  state, helper demand is empty, both findings are NORMAL, and root Target
  demand is nonempty.
- Existing sink seeds keep only observation 1 after run-5. Fresh source
  permission for the warm whole-object input ends in run-6; its NORMAL
  record and report stay cached. The field-input permission is renewed.
- The retained direct-read witness survives additional saved replies. Its
  output is exact and unprotected; no real field cut occurs in the steady
  step. Its mark-changing shape does not enter FLOW or NE retirement cells.

No iteration ceiling is part of that induction. A finite capture alone is
not a proof. Only `propext` and `Quot.sound` may occur in theorem axiom closure;
there is no classical choice, custom assumption, placeholder or external
decision oracle.

```bash
python3 spec/lean/proposals/provisional-must-cycle-20261115/check.py \
  --out /tmp/provisional-must-cycle-proofs
```

The checker copies and compiles five modules outside the repository, audits
every new theorem, and saves source hashes in `receipt.json`. Its source
scope is the fully analyzed synthetic unary producer/observation cone, with
two complete actual inputs and typed root controls. Ordinary untouched
identity/ZERO completion contributes no U and is outside the returned cone.
This is not a proof of whole-engine or Java-front-end equivalence.

The native test uses the actual actor, rules, calls, saved-record lanes,
handoff and stopping policy. From run-6 onward, the helper has no analyzer;
the continued root demand comes from saved replay. The tests change no
production operator. The test also checks the smaller backward producer-hit
set. The three control tests retain the previously rejected
one-input hypothesis: its paired C5 refinement finishes at run-5.
