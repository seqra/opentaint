# Different-path uniform reply cycle

Follow [proof-guide.md](../../../proof-guide.md). This is a counterexample to the support-only revision of
the [consolidated policy](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md),
including its latest definite EXACT/MUST reply support law. It proposes no
repair. Production is unchanged.

Current status: the proposed definite native MUST matching rule resolves
this case at **run-5** in its complete cold reference. The historical
counterexample and proof below remain unchanged.
[Current proof](../definite-must-replay-20261116/README.md).

Two straight-line owners use ordinary allocation, calls and return, plus two
unary conditional marking rules. There is no loop, recursion, cleaner, pass
rule, alias, unresolved method or intrinsic MAY producer. The two full marks
are distinct. The marking actions generate U; they do not copy a T suffix.

```text
retained NORMAL: p.MUST/T   -> ret.MUST/U
retained NORMAL: p.f.MUST/T -> ret.f.MUST/U
actual:         p.f.MUST/T,N

saved replay:   ret.MUST/U,D + ret.f.MUST/U,N
```

The literal paths differ. The second reply cannot absorb the first under
the selected identical-key law. Extra normal `p.g` guard records cannot
match the actual `p.f`. The backwards view of the broad record requires
MAY/T, which the actual marking at a.f satisfies again.

`DifferentReply.lean` includes base NE C2, qualified demand heads, bounded
child preparation from those heads and retained normal guards, raw-image
C5, paired selection, relative cuts, same-layer MUST canonicalization and
the actual `DefiniteReplySupport.foldValues` function. MUST retains its
dedicated uniform query at compatible heads. No concrete STAR coarse read
is removed by the FLOW-only child-routing rule. All relevant paths fit one
field, so cuts and increasing limits cannot alter the recurrence.

| Proof | Result |
|---|---|
| `cold_run1`–`cold_run6` | Executable cold prefix, including all seven paired run-2 rows and seven retained NORMAL records |
| `prepared_children_are_enabled_in_the_cold_run` | The qualified f child and the additional g query are included |
| `actual_packet_is_different_not_identical_support` | Latest reply filtering leaves root MUST/D, f EXACT/N and f MUST/N |
| `no_normal_root_reply_can_absorb_the_witness` | The actual packet has no NORMAL root reply |
| `added_g_guards_cannot_supply_the_f_actual` | The extra precise guard records cannot close the gap |
| `uncapped_recurrence` | `history(n+6)=s6` for every natural n |
| `no_early_stop` | Every completed run has outgoing root Target demand |
| `root_target_repeats_forever` | Repeated `ZERO -> DemandTarget` without any iteration bound |
| `no_current_helper_work_remains` | The repetition persists with empty helper demand |
| `both_reports_are_already_normal` | Both observations are confirmed by run-5 and remain so |

The model covers the complete T-to-U and Target/source-permission cone of
this two-owner sample. Untouched T identities and control identities cannot
create U; no data escapes the void root. Native adapters check the precise
MUST matching cells, reversal, packet canonicalization and latest support
filter. This is not a whole-engine bisimulation or a termination result for
arbitrary programs.

Validation: **31 new constructive claims; 2,331 audited claims in 116 modules**
with source-hash-checked dependencies. Only `propext` and `Quot.sound` are
allowed. No custom assumptions, holes, classical choice or external decision
oracle is used. The native class has **3 passing tests**; its finite driver
capture completes **run-31** with the policy limit. That capture is not the
uncapped proof. The independent latest-policy model is the uncapped proof.

```bash
python3 spec/lean/proposals/different-uniform-reply-cycle-20261116/check.py \
  --out /tmp/different-uniform-reply-proofs
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.DifferentUniformReplyCycleTest
```

`--dependencies DIR` reuses the definite-reply proof build after checking
every recorded source hash. The new module is compiled and axiom-audited
again. Compiled files and bulk logs stay outside the repository.

[Code, full iteration annotations, native/reference distinction and proof](../../../../docs/reports/bidirectional-different-uniform-reply-nontermination-20261116.md).
