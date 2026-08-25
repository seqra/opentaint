# Absorbing the prepend: what shipped, and what conductor says about it

**Status:** implemented and measured. Companion to
`2026-08-25-any-unroll-absorbing-prepend-design.md` (**D§n**), which is the design; this document
records what was built, what was deliberately *not* built, and what the conductor single-endpoint arm
measured.

**Harness.** `opentaint-w3-benchmark-results/scoped-harness/`, conductor +
`WorkflowResource#rerun` + `rulesets/single-rule`, `-Xmx8g`, IFDS budget 300 s, both diagnostics on
(`anyManagerDiag`, `apOpDiag`). Baselines built from `378b8a724`, the last commit before this work.

---

## 1. What shipped

| step | commit | what |
|---|---|---|
| −1 | `56c0772f8` | the subtree probe on the existing absorb — the one step that can *gain* a finding |
| 0 | `f1c0c5a89` | the `[any]` population on the progress line |
| 1 | `59da25045` | the reverse index, and the two remap loops that close the retention hole |
| 2 | `85ba9914e` | `AnyUnrollKind` and `anyUnrollKindMerge` |
| 3 | `3cacaf4fe` | the read records past the limit; `readChildPaidOnly` keeps the old contract |
| 4 | `a3411d030` | `writesAbove` / `absorbInto`, and the shadow probe that took the measurement |
| 5+6 | `16090d6c6` | `create` becomes `installAbove`; the graft gets the list-to-list form |
| — | `e8d6900fb`, `ecc36c027` | the round-trip closure test, R11, Appendix D |

**Step 4b — the subset construction on the reversed automaton — was NOT built.** §4 is the number
that decided it, and D§5.8(i) is the clause it answers.

---

## 2. TBD: the arms

---

## 3. TBD: what the counters say

---

## 4. TBD: step 4b

---

## 5. TBD: what to do next
