# Historical guidance control and local DATA bridge checks

The small loop program also misses its exact T observation on the complete pre-canonicalization runtime `52f32dd437d438aec4a700a02c18d94c31d58093`. The latest reached, completed and accepted iterations are **run-5 / run-5 / run-5**, with `COMPLETE / NO_DEMAND_EDGE` and zero NORMAL reports. The process then exits 1 at the unchanged expected-one-report assertion. This establishes that this small-program miss predates `8331bf9e`. It does not identify its first executed cause or prove that a new admission policy is needed.

The current storage repair also passes five local DATA bridge tests. The latest default command passes with **3,040 available results**, zero failures, errors or skips: 2,578 fresh core results and 462 reused JVM results. The native end-to-end gate remains red. These are separate results.

The [portable evidence](data/bidirectional-guidance-historical-control-and-data-bridge-20261106.json) embeds 43 artifacts and passes 46 static checks. It contains the complete program before and after its diagnostic-only change, init and runner scripts, historical log and root receipt, all historical source-file pins, relevant runtime sources, bridge test source/XML/log, and latest full-suite receipt/log. It also embeds the frozen source-history audit. No previous report or receipt was rewritten.

## Same program on the complete 52f runtime

The fixture has four methods, one exact T source rule and one exact T observation. Its field effects are:

```java
s = sourceT();                           // initialized source object
do { temp.g = s; next.f = temp; s = next; } while (again);
mapped = mapper(s);
observeExactT(mapped.Element.h);

mapper(q) {
    if (flag) out.Element.h = getG(getF(q));
    else { root1 = q; root2 = root1; out.Element.h = root2; }
    return out;
}
getF(q) { return q.f; }
getG(q) { return q.g; }
```

All required objects and the Element slot are initialized. The native finite IR models these field transfers directly. After the first loop iteration, `s.f.g` is the source object. The getter branch can return it at `mapped.Element.h`. There is no ND condition, GROUP mode, STATIC operation or explicit alias path. No summary, demand, initial fact or source permission is supplied by the fixture.

The historical control uses all **5,279 tracked blobs** from the exact 52f Git tree, not selected old files over a newer engine. All source pins pass before and after execution. The four fixture helper files are byte-identical between 52f and current. The only harness change replaces the later `SpatialCanonicalKt` CodeSource print with the existing historical `ApOps` CodeSource print. The program, rules, IDs, CFG, limits and assertions are unchanged.

Root ran a cold build: all 76 Gradle tasks executed. The child uses FULL mode, field limits `1,1,2,3,...,9`, 1 GiB heap, one CPU and a 20-second engine budget and task timeout. The parent uses Java 21, a 2 GiB in-process build and a fresh Gradle registry. These are diagnostic controls, not historical performance measurements.

The embedded `historical52f/root-historical52f.log` records:

| Lines | Actual evidence |
|---|---|
| 161–164 | Exact 52f revision, child JVM arguments and ApOps loaded from the fresh historical main output directory |
| 170, 172, 174, 176, 178 | Runs 1–5 all COMPLETE, at limits 1, 1, 2, 3, 4 |
| 179 | `firstReport=null`, `normalReports=0`, natural `COMPLETE / NO_DEMAND_EDGE`, run 5, FULL |
| 180 | Expected-one-NORMAL-report assertion fails |
| 196 | `76 actionable tasks: 76 executed` |

The log is not a compile or setup failure. The returned analysis report precedes the assertion. The raw root receipt keeps its original `TERMINAL_REQUIRES_OUTCOME_REVIEW` label; this report supplies the verified outcome classification without changing that receipt.

## What the history does and does not establish

The scalar rejection appeared in `c347ff8bb74e78062c3ae8162c8a0e9a2074f398`, before 52f. Its parent FLOW emitter used overlap followed by `flowForm`; the new policy explicitly rejects equal-path ANY demand with STAR actual. The policy bytes are identical at 52f, 8331, 4182 and current.

Both 52f and current replay saved NORMAL summaries before C2. If a suitable saved row exists, it can answer a call without a new initial or actor. The current frozen snapshots do not enumerate the full saved-record directory. The prepared next capture has no result used here. Actor absence is not proof that saved replay was unavailable.

The 52f run records completion and the miss; it does not trace the first lost fact. Its source already contains early MAY-prefix subtraction. Thus an inherited upstream loss can prevent it from reaching the same getter cell recorded on current. The [current storage report](bidirectional-concrete-guidance-repair-reproducer-20261106.md) separately shows the repaired B2 point loss and the remaining source-derived getG C2 rejection. Neither result makes a new C2 rule necessary or sufficient.

## Five local DATA bridge tests

`ProtectedAdmissionDataBridgeTest` passes all five tests, with zero failures, errors or skips. For each incremental step, it restores the **same current rows** in two groups. One group erases protection H and performs one ordinary no-H admission. The other admits the protected offer. It compares their DATA regions and independently checks literal protected and guide coordinates.

| Test family | Required result |
|---|---|
| STAR T4 exclusion weakening | Keep the whole mixed-content delta, in either H arrival order; duplicates add nothing |
| Existing STAR beside later ANY | Restore current state directly; do not re-admit and compact its old STAR row |
| Effective EXACT H in mixed wrappers | Ignore wrapper tail/E for exact coordinates; do not spread H to spans |
| MUST hole fill and exclusion join | Keep derived plain Empty-E DATA and the original protected header; do not protect the derived header |
| DEMAND/ANY guides with partial H | Retain root/child positions in one packet and both orders, with only supplied H; duplicates add nothing |

The H oracle is literal typed union. The guide oracle is literal union of supplied DEMAND/ANY coordinates. Delta checks require completeness and no invented annotation; every H bit needs a literal DATA carrier in the same packet.

The DATA comparison uses finite `f/g/h` paths through depth 3 and full marks T/U. Its no-H baseline is the current production admission path, including the selected guide law. It is not an independent complete oracle for old DATA behavior. Explicit T4 and MUST witnesses supplement the finite region checks. These tests do not prove all adapters, a global batch normal form, DATA order independence, a universal STAR suffix relation or native program recovery.

The final default command includes all five bridge tests. Its 438 XML files contain 2,578 core and 462 JVM results, all clean. Core XML timestamps are 19:05:10–19:06:08 UTC. `latest-full/full.log:5338` says `opentaint-jvm-dataflow:test UP-TO-DATE`; its reused XML timestamps are 17:46:34–17:50:00 UTC. The command exits 0 at 19:06 UTC. This is not a claim of 3,040 fresh test executions. The earlier frozen 3,035-result report remains unchanged.

## Evidence seals and limits

| Input or result | SHA-256 |
|---|---|
| Historical root receipt | `954852770ff7821c9613374d86117f4f6ca8b89ede10a4a98910b17cbb255122` |
| Historical full log | `29eb970133df72bc8b39e9cc6fae9b1692fcd306c0d0baf2d9d597fcb322808d` |
| Unchanged analyzed-program source | `8165143d74e738d69bd36d525b60a0b8948d8836b1803abc0f52bbfa8ba5ec59` |
| Historical diagnostic-print source | `8873ce2c8143077096cc2b410ab7281cc3909a2d14ccc19a9d5bd276261dd96b` |
| Bridge test source | `d335a105334cae5bac35beb8da82a1d40cf3ac0112803f3f3871d5912bd71719` |
| Bridge root receipt | `3908f1c7e88e2ea9b0d5da235806316e551c6ea9aadbe3ccdabdef6aab96b26b` |
| Latest full-suite receipt | `2203aa16b816a4331c3ee982c60033613ff0cb8bc532fdc13432b229352291e4` |
| Portable evidence JSON | `ae4498876ab9874a1d1b2c57f3d6debd7670d8145180993a85787b2b57f73f5c` |

The three current storage source hashes match the bridge and final-suite receipts. The selected storage specification adds no C2 policy change. No f945 real-project baseline or new real-project campaign was run. These results do not establish a final Conductor cause, a safe new admission policy, progress or termination. Root owns all executions; the reporting agent launched none.
