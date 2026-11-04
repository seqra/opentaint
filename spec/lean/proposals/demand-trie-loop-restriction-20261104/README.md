# Demand-trie loop-restriction geometry

Status: **PROPOSAL MODEL ONLY — no Kotlin implementation**.

```sh
python3 spec/lean/proposals/demand-trie-loop-restriction-20261104/check.py
```

The executable prefix-list reference consumes the complete compatible demand
paths **after** correct scope, route, direction, base and concrete FULL-mark
selection and the native pre-admission guard. In particular,
`MethodBlockRuntime.initials` checks
`keepLocalConclusion(scope.block, scope.entry, actual, count=false)` before
querying demand. A row from a scope whose local-conclusion guard rejects the
unchanged base cannot supply a boundary witness, even if its key is absent
from the raw baseline. Filter the precision forest by these existing guards
per `(scope, base)`; unknown guard views provide no certificate and require
native fallback. All modeled cuts preserve the base. Every field is counted;
static anchors and uncounted accessors are
outside this model. For raw path `p`, it retains
`p.take(1 + max[d in D] LCP(p,d))`. The independent node walk from the pinned
earlier geometry module is proved equal to this full-list reference. It keeps
the first distinguishing raw field for every demand, not merely for one
longest terminal. Its depth is bounded by the deepest requested path plus one.

The scalar C2 subset models matching concrete FULL marks, empty E, nonstatic
counted paths, EXACT/ANY demand tails and EXACT/ANY actual tails. Its image
contains the entire initial path, tail and layer. A constructive geometric
certificate proves that a strict prefix cut preserves this complete image
for every compatible row. The finite checker verifies the certificate from
prefix relationships and lengths; it does **not** assume C2 output equality.
Identity projections preserve the original tail and layer.

The requested examples use `f=0,g=1,h=2,k=3,z=4`. Raw `f.g.h.k` with demands
`[f],[f.g]` cuts to `f.g.h/ANY`; demands `[f],[f.g.z]` also retain `h` to
distinguish the sibling `z`. Both terminal payloads remain present. The model
also proves a raw MAY counterexample to trie minimality, so geometry/image
preservation is **not** a theorem that the trie gives the first native cut.
The model also constructs a maximum-LCP boundary witness. Its ANY demand emits
one constant MAY/DEMAND key throughout earlier MAY ancestor cuts; absence of
that key from the raw baseline certifies that the earlier range can be skipped.
The first-accepted search theorem requires that certificate explicitly.

Read [REPORT.md](REPORT.md) for the exact scope and remaining adapter
obligations. [checks.json](checks.json) records the kernel check and
[audit.txt](audit.txt) audits its public declarations. No runtime or experiment
is included.
