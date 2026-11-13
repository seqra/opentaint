# Coarse observations do not prove eventual coverage

This model supports the current OWASP target `1025a197…` investigation. It does not classify a demand row. The compatible fresh capture reached run-11, completed run-11 and accepted run-11. No new scan was made for this check.

For a fixed premise and mark, empty exclusions, and an unprotected result,
let `f != g`. Compare results within each row's layer:

| Input class | Existing output | Extra branch output | Canonical result |
| --- | --- | --- | --- |
| Coarse MAY | root.MAY, DEMAND | root.f.MAY, DEMAND | root.MAY, DEMAND |
| Coarse MUST | root.MUST, NORMAL | root.f.MUST, NORMAL | root.MUST, NORMAL |
| Precise point g | root.g.EXACT, NORMAL | root.f.EXACT, NORMAL | Both points |

`CanonicalObservationGap.lean` proves equal coarse observations for any number of alternating MAY/MUST rounds. It also proves that the later precise input gives a different output. All six axiom lists are empty. Thus, canonical history is not an injective description of the transfer relation. The model does not claim that the selected method has this extra branch, or that the complete historical input set contains only these two coarse classes. The native body check must test all actual initials, including EXACT companions.

## Current native service check

The fixed source-pinned scalar probe reads all 31 NORMAL coordinates and all six retained demand rows. For the hypothetical relation:

```text
ret.f.*/FLOW -> arg(1).bytes.g.*/FLOW, NORMAL
```

only selected row X preserves the result through paired C5. The retained root-MAY sibling admits the same initial, but rejects this output. The conclusion has field length 2, equal to the row-relative budget `FL(bytes) + 1`.

The opposite MUST providers can independently return these caller facts:

```text
ret.f.$/T, NORMAL -> arg(1).bytes.[any]/T, DEMAND
ret.f.$/T, NORMAL -> arg(1).[any]/T, DEMAND
```

These facts do not, by themselves, publish the missing owner relation. They can retain a caller source route while the owner lacks a route to publish the suffix-changing relation. This is a missing proof obligation, not a demonstrated sink loss.

## Required eventual-coverage certificate

A future candidate must supply both of these witnesses:

```text
service cell of X
  -> retained native caller route
  -> retained owner admission AND paired output route
  -> exact required service, or a strictly smaller refinement obligation
```

The rank must decrease on every nonterminal refinement step. A rank on an unchanged coarse MAY coordinate cannot decrease on a self-return. A rank on the complete engine state is not excluded by this small model.

The certificate must cover arbitrary later inputs and field limits. Equal finite histories do not supply that invariant. A finite symbolic service graph with an executable decreasing rank could be a stronger edge-only predicate. Its symbolic partition and native re-entry bridge remain to be proved. No such certificate has been established for this target, so it must not be batch-applied as a new elimination pattern.

External evidence:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/
  redundant-demand-rows-20261112/cases/owasp-1025-eventual-must-cover-audit-v1/
```

`native-receipt.json` covers scalar native C2/C5 and saved MUST reads. `lean-receipt.json` covers only the small canonical-observation model. Neither claims an actual body derivation, a deletion result, necessity or future closure.
