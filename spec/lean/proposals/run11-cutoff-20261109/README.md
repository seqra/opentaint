# Run-11 cutoff laws

Selected execution policy: default bidirectional scans stop after completed
forward run-11 when refinement remains. Genuine empty-demand completion has
priority. RUN_LIMIT records a cutoff, not convergence.

Run with Lean4.35.0:

```sh
lean Cap.lean
lean Reports.lean
```

The cap model proves twelve local laws and has two executable witnesses. It uses
no Classical.choice, excluded middle, sorry or custom axioms. The bounded
schedule witness is closed computation. Two general lemmas use Lean's propext
and Quot.sound through propositional/arithmetic proof tools. These are local
control-flow laws; native tests connect them to the driver barrier.

Reports.lean proves ten finite report/snapshot laws and has three executable
examples. It proves confirmed retention/priority, latest-only provisional
membership, forward replacement, backward retention and uncommitted-barrier
retention. Post-commit cleanup failures keep the existing native contract.
It uses executable list operations, with no classical choice.
Reports.axioms.txt records its standard Lean dependencies. These laws do not
prove concrete reachability of a provisional local sink witness.

See [source-proof.md](source-proof.md) for the pre-implementation native
correspondence, selected semantic scope and test obligations.
