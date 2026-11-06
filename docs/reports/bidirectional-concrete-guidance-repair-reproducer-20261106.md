# Concrete guidance storage repair: fixed point loss and remaining admission gap

The storage repair retains the fine B2 guide that the native loop example lost before the repair. The end-to-end example still has no NORMAL report. The latest reached, completed and accepted iterations are **run-5 / run-5 / run-5**, with `COMPLETE / NO_DEMAND_EDGE`. Its unchanged assertion then fails because it requires one NORMAL report.

The remaining observed route reaches the second getter with NORMAL `g.STAR/FLOW` metadata. Its frozen demand asks for `g.ANY/FLOW`. The unchanged C2 policy rejects this same-path pair. This is a separate admission gap, after the repaired point-store loss. No admission-policy change is included here.

The [portable evidence](data/bidirectional-concrete-guidance-repair-reproducer-20261106.json) embeds 98 artifacts, with full text, byte counts and SHA-256 hashes. It includes the program, three complete capture logs, snapshots, source and observer pins, old first-loss evidence, test receipts, patches, and local policy witnesses. All 44 static checks pass. No external capture is needed to inspect the recorded facts.

## Small native example

The finite IR fixture has four methods, one exact T source rule and one exact T observation. This listing states its field effects. All objects and the `Element` slot are initialized; allocations below state that precondition. The native fixture models the transfers directly.

```java
root() {
    temp = new Box(); next = new Box();
    s = sourceT();                         // initialized source object
    do {
        temp.g = s;
        next.f = temp;
        s = next;
    } while (again);
    mapped = mapper(s);
    observeExactT(mapped.Element.h);
}
mapper(q) {
    out = new Result(); out.Element = new Slot();
    if (flag) out.Element.h = getG(getF(q));
    else { root1 = q; root2 = root1; out.Element.h = root2; }
    return out;
}
getF(q) { return q.f; }
getG(q) { return q.g; }
```

After one loop iteration, `s.f.g` is the source object. The getter branch can place it at `mapped.Element.h`. Source and observation are native rules, not extra analyzed methods. The fixture has no ND condition, GROUP mode, STATIC operation or explicit alias path. It injects no summaries, demands or initial facts.

Below, B2 means backward run-2; F3 means forward run-3, at field limit 2. `$` means EXACT. `Element` is a field slot, distinct from the STAR tail. Trace aliases are `s=var(0)`, `mapped=var(1)`, `gotF=var(11)` and `arg0=arg(0)`. Field IDs are `f=0`, `g=4`, `h=8`, `Element=11`; full T has ID 1. All decisive cells have empty exclusions, empty FLOW mark exclusions and no protection.

## The old point loss is fixed

The old 113-check transaction audit identified a real loss at B2 point 5: under premise ZERO, scope `(block 3, entry -2)`, offering `s.f.ANY/T DEMAND` after `s.ANY/T DEMAND` produced no fresh fact. The retained bucket lacked the child. The first loss was in `TaintGroup.subtractSubsumed`, before state canonicalization.

The repaired capture records the same typed coordinate and full premise:

| Actual stage | Embedded log and line | Result |
|---|---|---|
| Point transaction 8, after `g` offer | `post-repair-point-capture/root-capture.log:189`, sequence 58 | Fresh `s.g.ANY/T DEMAND` |
| Point transaction 11, before `f` offer | same log, line 204, sequence 73 | Offers `s.f.ANY/T DEMAND`, ZERO, scope `(3,-2)`, point 5 |
| Same transaction, after admission | same log, line 205, sequence 74 | Fresh count 1; fresh fact is exactly the offered `f` guide; retained `s` bucket has root, `f` and `g` |
| B2 joined scoped summary | `forward3-full-capture/root-capture.log:133` | ZERO paired with all three `s` guides; selected for handoff to `(3,7)`, exit `-2` |
| F3 incoming adjacent scope | same log, line 141 | Root, `f` and `g` concrete entries each paired with ZERO exit, port `-2` |

The F3 root trace also keeps the source-backed `s.f.g.$/T NORMAL` at loop exit 7, then offers it to adjacent scope `(3,7)`, point 5. See `post-repair-point-capture/root-forward3.log:214–216`, sequences 69–71. Sequence 77, line 222, records a fine exact-T initial and a NORMAL `c5-normalized` candidate. That candidate does not establish final C5 admission or a report.

## The remaining getter boundary

The complete F3 snapshots record:

| Recorded item | `forward3-full-capture/root-capture.log` | Full relevant coordinate |
|---|---|---|
| getF joined NORMAL summary | line 164 | `P=INITIAL #21: arg0.f.g.STAR/FLOW` → `ret.g.STAR/FLOW NORMAL` |
| Mapper processed input at call node 3 | line 163, row 21 of 46 | Same P; `gotF.g.STAR/FLOW NORMAL` |
| Complete getG public demand | line 144 | `arg0.g.ANY/FLOW` → `ret.ANY/FLOW`; no other public, control or scoped rows |
| getG joined/processed state | lines 166–167 | Actor absent; zero joined rows and zero processed inputs |

The unchanged call binding maps `gotF` to callee `arg0` and preserves the relative path, tail, layer and mark exclusions. Thus the recorded input gives this C2 cell:

```text
demand entry = arg0.g.ANY/FLOW
bound actual = arg0.g.STAR/FLOW, NORMAL
same path g; base, mark and field-budget checks pass
RestrictedInitialPolicy: demanded ANY + actual STAR => null
```

This is a **source-derived evaluation of the recorded input and complete demand snapshot**, not a logged rejected-C2 callback. `RestrictedInitialPolicy.kt:30–32` returns null in this branch before admission-layer selection. The actual actor absence and zero processed count support the boundary diagnosis. They do not prove that this is the only remaining obstacle, or that a C2 change alone restores the report.

Three isolated native tests pass against the unchanged policy: current rejection, ordinary NORMAL STAR/FLOW and exact-T `f/g` transport, and a wrong-field negative case. A checked 12-lemma local model establishes the corresponding rejection and ordinary suffix transport. Neither result proves a new admission rule, progress, termination or end-to-end recovery. A separate source-only audit identifies a possible prefixed local recurrence risk; it does not derive actual packet resupply or a whole-driver cycle. The admission decision remains pending.

## Validation and retained red gate

| Check stage | Tests / failures / errors / skipped | Result |
|---|---|---|
| Clean storage RED before repair | 19 / 15 / 0 / 0 | Expected storage assertions fail |
| Selected storage GREEN | 19 / 0 / 0 / 0 | Pass |
| First default command after repair | 3035 available / 20 / 0 / 0 | Old expectations fail |
| Latest default command after test-only updates | 3035 available / 0 / 0 / 0 | Exit 0 at 18:32 UTC |
| Isolated admission/transport witnesses | 3 / 0 / 0 / 0 | Pass; current rejection retained |
| Optional native program | 0 NORMAL reports; accepted run-5 | Exit 1 at the expected-one-report assertion |

The latest default command ran 2,573 core tests. It reused 462 successful JVM results: `full.log:5332` says `:opentaint-jvm-dataflow:test UP-TO-DATE`. The JVM XML timestamps are 17:46–17:50 UTC; fresh core XML timestamps are 18:31–18:32 UTC. These are 3,035 available clean results, not 3,035 fresh executions.

The two test-only patches adopt the selected DEMAND/ANY guide and protected-coordinate laws. They keep scalar DATA coverage and C2 policy unchanged, add supplied guide coordinates to storage oracles, and use `addAll` where a delta can have multiple headers. They retain ordinary MUST/STAR controls and full-premise/scope checks. The optional program and its expected-one-report assertion are unchanged.

The B2, F3-root and F3-all-method captures emit respectively 203/203, 130/130 and 13/13 events, with 12, 12 and 20 complete frozen snapshots. All report zero trace drops, encoding errors and sink errors. Observer blocks strip back to the pinned native sources; the all-method observer reads frozen rows directly. Root ran the captures with 1 GiB/one-CPU/20-second diagnostic children. This report added no runtime jobs.

From `core/`, the separate optional gate is:

```bash
./gradlew -I ../scripts/loop-boundary-reproducer.init.gradle \
  :opentaint-dataflow-core:opentaint-dataflow:runLoopBoundaryPrecisionReproducer \
  --no-build-cache --max-workers=1 --console=plain
```

## Source and patch seals

The captured storage repair is a working-tree patch over `e6fbda8e17934a2059b1fa3069cebcb4692ce9c7`. The evidence contains complete bytes and exact hashes for these inputs:

| Input | SHA-256 |
|---|---|
| `Groups.kt` | `6e0dc30e4151a57d56bbf98afc65781122343db0d3a79fad4aaa86b30ec34eac` |
| `SpatialCanonical.kt` | `daea564174ac8bd837c70ed4ca3598fd63690686db855047f96810c7318a1608` |
| `DiagonalRelations.kt` | `5080f41a2d1953ea98e73686d3f90db5da8a621cec4b8746545d99e0bae5a781` |
| Runtime three-file patch | `df3d74e663bf38dceb979fbab68b1278655681c5caabcc362adf2ebd96cc21d1` |
| `expectation-updates.patch` | `c4344203a553662a7dcc6d429953c9504847ec99ed5a2e373214ca8f6b94414b` |
| `taint-admission.patch` | `748335479600af41fa18f669034db6fa595b2fc8d7622870836d1377efb87276` |
| Unchanged C2 policy | `dcbaee551ecdae33590c56ef0154bfd0ef419c8c8fa3dc7b38127006a73ad44e` |
| Unchanged optional program | `8165143d74e738d69bd36d525b60a0b8948d8836b1803abc0f52bbfa8ba5ec59` |
| Portable evidence JSON | `b6e9a5b0beabd40e667ab6b789a47174286c738e8c44a1a1ada596e716e4b0c1` |

No new real-project campaign was run. These results do not establish a cause for the final missing Conductor findings. Storage recovery, local admission witnesses and the passing default gate remain separate from the still-red native end-to-end result.
