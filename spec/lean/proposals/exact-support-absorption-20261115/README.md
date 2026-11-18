# Exact FULL reply support absorption

Follow [proof-guide.md](../../../proof-guide.md).
The [consolidated approach](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md)
contains the contract. Production is unchanged.
[Validation and annotated run-7](../../../../docs/reports/bidirectional-exact-support-absorption-20261115.md).

One new semantic rule: in a complete ready reply batch, retain a NORMAL
concrete exact point and omit its identical DEMAND copy. Compare the complete
caller original, owner/direction/scope/ports, continuation, full mark and
literal H. Real exact E/mx must be empty. Keep all unsupported members.
Do not promote provisional support, remove native records or cancel Targets.

| Module | Checked claim |
|---|---|
| `ExactSupport` | Explicit retained witnesses; every NORMAL member and point key preserved; subset/idempotence/merge/order laws; arbitrary finite support-monotone continuations; complete ND binding retained; literal scope/origin/continuation/H separation; uncertain tails retained |
| `ClosedCycle` | Actual selected C2/C5 and native definite/provisional MUST cells; unchanged cold runs 1–6; natural empty DATA/Target frontier at run-7; both reports and records retained; no uncapped revival |
| `PriorAcceptance` | Reply folding is inert on every captured packet at every iteration in the 18 prior cold references, plus the protected uniform closure replies |

The unchanged counterexample is compiled separately as `MustCycle` from its
original source. Its uncapped nontermination proof still passes. It models
the previous rule; `ClosedCycle` models the new one. No hard ceiling appears
in the new stopping proof.

The cold new proof deliberately leaves current replies asynchronous: a
provisional saved reply can reach the observer before the new NORMAL reply
in run-5. That Target is not retracted. By run-7, both records are ready in
the saved batch, so no new DEMAND point or Target is produced.

```bash
python3 spec/lean/proposals/exact-support-absorption-20261115/check.py \
  --out /tmp/exact-support-proofs
```

`--dependencies DIR` can reuse the previous point-write proof build after
checking every source hash. The new modules and the old MUST counterexample
are compiled and axiom-audited again. Compiled files and receipts remain
outside the repository. Only `propext` and `Quot.sound` are allowed.

Scope: constructive AP/support and reply-batch models, including typed root
controls. The continuation theorem describes operators whose output support
is the native input/loss join and whose transfer key is layer-independent.
It is not a whole-engine equivalence proof. Native integration must preserve
all existing resume coordinates, pending demotion and observation order;
resolved layer-sensitive alias branches must remain separate until their
existing effects have run or their continuation routes agree;
the component adapter validates committed native replies. No blanket MAY,
NE, STAR, FLOW or Target coverage rule is proved here.

The native production counterexample still reaches **run-31**, policy ceiling.
The new reference completes **run-7**. Old complete references retain their
individual stops, latest **run-15**; protected closure **run-3**, standalone
selected cleaner **run-1**.

Latest build: **67 new audited theorems; 2,180 declarations in 109 modules**
including the reused, source-hash-checked old proof build and the unchanged
counterexample. Native validation: **41 tests pass**, including five new
candidate-adapter tests. Those tests validate native committed replay outputs
and filter guards; they do not install a complete native batching protocol.
