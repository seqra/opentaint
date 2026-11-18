# NORMAL uniform FLOW coverage of NE

[Approach and regression matrix](../../../../docs/design/bidirectional-normal-uniform-ne-coverage-20261114.md).
Proposed egress law only; production remains unchanged.

- `UniformCoverage.lean`: conservative same-original FLOW/MUST-to-NE
  coverage, retained normal providers, executable spatial witnesses,
  arrival-order fixture, protected/concrete/STAR/MAY/backward rejection.
- `Closure.lean`: complete cold run-2 rows and run-3 packets for the old
  method-only example and the new ordinary double-write example. Both
  calls are computed; the second offer adds no query/summary and further
  closure rounds change nothing. Both root findings are NORMAL and all
  outgoing reference demands are empty at run-3.
- `Regressions.lean`: read/write BB composition, arbitrary longer uniform
  read suffixes, cleaner repair, wrapper h reader and unchanged weak
  reverse-MUST views.
- `VirtualProviders.lean`: legally reconstruct a same-original uniform
  view from a retained NORMAL record when old precoverage omitted a
  duplicate. Check warm-record completion, unchanged support layers and
  rejection of cuts, STAR originals and provisional/weak providers.

```sh
python3 spec/lean/proposals/normal-uniform-ne-coverage-20261114/check.py \
  --out /tmp/normal-uniform-ne-coverage-proof
```

The checker compiles the selected/proposal references and the ordinary
counterexample first. It audits every new theorem, rejects warnings,
proof holes and custom/classical axioms, and permits only `propext` and
`Quot.sound`. Source hashes and compiler logs go to the external output
directory. No result relies on an iteration limit.

Latest check: **PASS**, 17 modules, 292 audited declarations including
51 new declarations. Receipt:
`normal-uniform-ne-coverage-20261114/proofs-v4/receipt.json` in the external
report-data archive. The [annotated traces](../../../../docs/reports/bidirectional-uniform-ne-coverage-reference-20261114.md)
show the old and new references completing at run-3. Eleven existing
native reuse tests passed; they do not implement the new NE law.

Scope: qualified scalar positive field-transfer concept and closed
reference programs, with unchanged selected C2/C5/cut functions. Full
native alias/rule/record service correspondence remains an integration
obligation. Unsupported cases must retain current behavior.
