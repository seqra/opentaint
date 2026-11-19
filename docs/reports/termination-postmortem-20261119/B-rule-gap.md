# B — Rule gap: why proved termination rules are useless on real workloads

Read-only investigation of branch `saloed/bidirectional` (HEAD 758ad99ff). Nothing in the repo was modified, no build or benchmark was run.

## Sources and citation keys

| Key | File |
| --- | --- |
| SPEC | `spec/demand-refinement-and-termination.md` |
| PROTO | `docs/reports/bidirectional-demand-refinement-rule-prototypes-20261118.md` |
| COST | `docs/reports/bidirectional-useful-rule-cost-fixes-20261119.md` |
| PERF | `docs/reports/bidirectional-demand-refinement-performance-20261118.md` |
| BASE | `docs/reports/bidirectional-termination-baseline-run101-20261118.md` |
| CAT | `docs/reports/bidirectional-demand-termination-counterexamples-20261115.md` |
| VALID | `docs/reports/bidirectional-termination-fix-validation-20261117.md` |
| AUDIT | `docs/design/bidirectional-demand-termination-soundness-audit-20261117.md` |
| NOLOSS | `spec/demand-refinement-no-loss-audit.md` |
| PROOFIDX | `spec/lean/proposals/demand-refinement-spec-20261117/README.md` |
| TASK | `term-task.md` |
| ARCH | `/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/demand-refinement-rule-prototypes-20261118.n00xyl/` (external archive; per-rule worktrees, `source.patch`, `decision.json`, `native-diff.json`) |

Labels used below: **[R]** = stated in a report/spec, **[A]** = read directly from the archive receipts (raw data, not in a report), **[I]** = my inference.

Caveats on the inputs:
- Rule numbering drifted between the 17 Nov audit (AUDIT:118-151) and the current spec (e.g. R05/R06 swapped meaning, R17 removed, R19 changed from "completion omission" to "deliver every current reply"). I use the current SPEC numbering.
- CAT does not carry R-numbers for most entries. The rule-to-counterexample mapping is reconstructed from PROOFIDX:11-27 (rule -> proof package) and CAT:167-193 (example -> repair package). That join is **[I]**.
- "C2" and "C5" are stages (call-entry admission, paired summary restriction), not rules; "C2/C5 repair" in PROTO:205 means R20.

---

## 1. Rule table

Verdict legend: **USEFUL** = stopped at least one native run-101 fixture; **USELESS** = PROTO label (no natural stop added in the 92-case suite or the compiled OWASP `doSomething` entry); **NATIVE** = PROTO "native parity / dependency", no independent prototype; **COSTLY** = PROTO label for a single-pass RSS delta. "Projects: skipped" means no four-project run exists for that rule (PROTO:205-224).

All USELESS prototypes share the same receipt: `decision.json` = `"natural_stops": []`, compiled entry baseline and prototype both `["101","COMPLETE","RUN_LIMIT"]` **[A]**.

| ID | Intent | Motivation (CAT entry / phase) | Where it acts | Verdict and numbers |
| --- | --- | --- | --- | --- |
| R01-R03 | A real field cut emits NE (nonempty MAY) instead of MAY; NE read/write transfer | Root MAY renewal, BB renewal (CAT:580-660, proof `non-empty-may-20261113`) | per-edge transfer hot path, every cut, all runs incl. run-1 (SPEC:190) | **USELESS** (PROTO:205). First version stopped OWASP entry at run-5 but "lost confirmed observations elsewhere"; with R20 repair the stop vanished. Fixtures got worse: global cut 6 -> 302 pairs, nested replay run-65/511, overwrite run-64/522 (PROTO:255-259). [A] 26 failed tests, root MAY 4 -> 104, protected global cut 7 -> 469. Full implementation heap: 668,506 NE point memberships on Conductor (PERF:289), 2,528,831 on ThingsBoard (PERF:473). Projects: skipped. |
| R04 | Same-head `p.M <- p.M` also starts EXACT (`p.$`) beside STAR | NE split of the MAY admission family (same package) | per-offer C2 | **USELESS** (PROTO:206): "alternating conditional fixture grew from 4 to 7 pairs". [A] `R04/native-diff.json`: 11 cycle fixtures grew (e.g. alternating 4 -> 9, deeper-excluded 4 -> 11, excluded 4 -> 8, six others 4 -> 7 or 3 -> 5), none stopped. Projects: skipped. |
| R05 | NE selector drops the EXACT-at-own-head start | NE family | per-offer C2 | **NATIVE/dependent** (PROTO:230): "A baseline with only native tails has no NE row to drive these operations". Unmeasured alone. |
| R06 | Possible (D-only) binding of a deeper frozen `p.f.M` row to an ancestor `p.*` offer | Bounded refinement frontier (Root MAY) | per-offer C2 + current reply matching | **USELESS** (PROTO:207): "One deferred recursive control changed from natural run-5 to the run-101 cutoff". [A] `R06/native-diff.json`: eight WordChunk fixtures changed, two went natural run-5 -> run-101, others 5 -> 7, 5 -> 17, 5 -> 77, two became timeouts with 938 / 1028 pairs. Projects: skipped. |
| R07 | Copy the actual's real exclusion E onto the STAR start at the same head | "Real exclusion and unrelated output child" (CAT:428; `concrete-query-exclusions-20261116`) | per-offer C2 + raw C5 image | **USELESS** (PROTO:208). [A] `R07/native-diff.json`: `"changed": []` over all 92 cases, i.e. its own motivating fixture (`ExcludedGuardCycleTest`) still ends run-101; one component test fails by design. Projects: skipped. |
| R08 | Keep the deeper NORMAL MUST actual head + E (the only `FL(Dc)+1` exception) | "Deeper real exclusion" (CAT:382; `excluded-head-admission-20261116`) | per-offer C2 | **USELESS** (PROTO:209). [A] only a noise fixture changed; `DeeperExcludedGuardCycleTest` unchanged. Full implementation on Conductor: "This run records zero R08 overruns" (PERF:231). Projects: skipped. |
| R09 | Keep distinct `P->p.M` and `P->p.f.NE` guide rows; observed-first-field child plan | Nested saved replay (CAT:778) | handoff / demand preparation | **NATIVE/dependent** on NE (PROTO:230). Unmeasured alone. |
| R10 | Prepare one level of child starts (`p.f.$`, `p.f.*`) from deeper guides / saved guards | Nested saved replay; saved replay with real E (CAT:778-869) | per-offer C2 (cross-row lookup, marked COMPLEX) | **USELESS** (PROTO:210): global cut 7 pairs instead of 6; protected variant "completed run-99 before the fixture timeout, with 240 pairs instead of 7". Growth table H3 6 -> H49 127 helper pairs (PROTO:299-306). Projects: skipped. |
| R11/R12 | Run coarse read and prepared child through ordinary transfers; dedup after | Same | per-edge transfer, saved replay | **NATIVE** (PROTO:231): "additional admissible children belong to the R10 prototype". |
| R13 | Reject strict-descendant write-keep on an EXACT FLOW point | EXACT-origin nested write (CAT:871), "a supported synthetic atomic core form; no end-to-end JVM lowering result is claimed" (CAT:874-875) | per-edge raw transfer (field write) | **USEFUL + COSTLY** (PROTO:204): nested-write fixture run-101 -> natural run-3, provisional observation removed. Projects: same endpoints, 0/0 locations (PROTO:68-71); first pass Conductor RSS +0.439 GiB (PROTO:102). After cost fix: three R13 builds "all lost two completed Stirling-PDF iterations" (run-9/8/7 vs run-11/10/9; COST:464-469, 506-508); only the build with loop shortcuts matched native (COST:470-474). |
| R14 | Saved-first replay even when current C2 plan is empty | Nested saved replay | per-offer (call/block) | **NATIVE** (PROTO:232). |
| R15 | Saved MUST uses only definite lanes; keep provisional D reply | Direct concrete MUST replay, uniform saved reply, different-path uniform replies (CAT:958-1072, 520) | saved summary matching | **NATIVE** (PROTO:232). But its three fixtures are still `RUN_LIMIT` at run-101 natively (BASE:23). |
| R16 | Deliver each NORMAL and DEMAND reply; keep both memberships | Definite reply support | reply delivery | **NATIVE** (PROTO:233). |
| R17 | (removed) NORMAL MUST actual covers a whole D region | Alternating conditional generators (CAT:469) | reply admission | **Removed** (PROTO:237). NOLOSS:10 "R17 can lose a track while keeping its report". Replaced by R42. |
| R18 | Run C5 on a specialized candidate even if a saved NORMAL relation covers it | Global-cut growth / precoverage | summary publication | **NATIVE** (PROTO:234). PERF:613-621 names R18 as what *keeps* the OWASP cut alive. |
| R19 | Apply every matching current summary; NORMAL does not suppress DEMAND reply | Six "protected / unadmitted / exact input" entries were originally fixed by R19-as-completion (PROOFIDX:20) | reply delivery | **NATIVE** in its current (non-omitting) form (PROTO:233). The six fixtures stay `RUN_LIMIT` at run-101 (BASE:21-22). |
| R20 | C5 tests the raw C2 image before normalization | Phase-4 repair needed by NE (R01-R03) | summary publication (C5 entry test) | **USELESS** in isolation; "The rule is required for the tested NE integration" (PROTO:213). Full implementation hot path: `RestrictedInitialPolicy.rawWitness` 60 of 100 samples in OWASP run-11 (PERF:157-159), 24.71% / 26.93% / 34.58% of Stirling samples (PERF:495, 512-519). |
| R21 | Own-row scalar exit selection and `FL(Dp)+1` cut | NE family | C5 | **NATIVE/dependent** (PROTO:230). PERF:230 "R21 also widens the static FLOW search to concrete selector labels". |
| R22 | FLOW EXACT-to-STAR normalization needs a suffix-lifting witness | NE family | C5 | **NATIVE** (PROTO:234). |
| R23 | Keep distinct MAY and NE summary rows after C5 | NE family | summary store, handoff | **NATIVE/dependent** (PROTO:230). |
| R24 | Keep both when NORMAL MUST covers an admitted DEMAND region (default) | Global-cut growth (uniform NE coverage) | summary admission | **NATIVE** (PROTO:233); certified removal moved to R42. |
| R25 | Native aligned NORMAL FLOW subsumption + verified handoff compaction | Kernel proof | handoff | **NATIVE** (PROTO:235). PERF:623-631: "R25 cannot merge the shallow and deep pairs". |
| R26 | Selected EXACT root cleaner keeps NORMAL on same-head MUST under an observer guard | Uniform root cleaner (CAT:703) | per-edge cleaner transfer | **USEFUL + COSTLY** (PROTO:217): fixture run-101 -> natural run-1. Projects: "The single-root guard kept native cleaner transfer on all four projects" (roots: OWASP 8,401, Conductor 7,210, ThingsBoard 30,791, Stirling 3,719; PROTO:127-139). After fix: structural checks 32 -> 1 (COST:67); RSS deltas +0.045 / +0.011 GiB "smaller than the differences between the native samples" (COST:528-531). |
| R27 | Schedule ready EXACT/NORMAL/control work before uncertain work | Kernel order-independence | per-owner scheduler | **USELESS** (PROTO:211). [A] `"changed": []`. |
| R28 | Typed Target persistence, empty-frontier stop | Native invariant | handoff / stop test | **NATIVE** (PROTO:236). |
| R29 | Preserve literal protection H on transfer and cuts | Native invariant | per-edge | **USELESS** (PROTO:212). [A] `"changed": []`. |
| R30 | Complete ND (AND) application | Native invariant | summary application | **NATIVE** (PROTO:236). |
| R31 | Mask only FLOW leaves whose suffix cone intersects the cleaner | Phase-3/4 soundness: cleaner/getter admission loss (CAT:115-120; AUDIT:121) | per-edge cleaner transfer | **USELESS** (PROTO:214). [A] one soundness fixture changed its observation set; no stop. |
| R32 | Backward run-2 same-head STAR relay | Phase-3/4 soundness: nested overwrite gap (CAT:99-106) | per-offer C2, run-2 only | **USELESS** for termination (PROTO:215); **catastrophic cost** in the full implementation: Conductor run-2 41.308 -> 219.120 s, OOM (PERF:89); carry-only ablation D4 completes run-2 in 183.584 s (PERF:384); 1,074,625 of 1,076,995 same-head STAR offers (99.78%) come from shared static carry (PERF:368-370). |
| R33 | Clear FLOW mx on projected demand endpoints | Existing native invariant made explicit | handoff | **NATIVE** (PROTO:236). |
| R34 | Possible saved direct STAR read on a shorter STAR offer | Phase-3/4 soundness: prefix-return loss, old case 165 (CAT:1196-1208) | saved summary matching | **USELESS** "for termination. The native component comparisons recovered observations in two broad-read cases" (PROTO:216). |
| R35 | R26 below the root (descendant EXACT cleaner) | Descendant selected EXACT cleaner (CAT:170) | per-edge cleaner transfer | Direct slice **USELESS**; closed-callee variant **USEFUL + COSTLY**: run-101 -> natural run-1 (PROTO:218). "The guard stayed inactive on all four projects." After fix: checks 32 -> 1 (COST:68); ThingsBoard quiet repeat 183.937 vs 184.278 engine s (COST:546-548). |
| R36 | Partition surviving NORMAL MUST after a deep subtree clean | Nested ALL/BELOW cleaner (CAT:171) | per-edge cleaner transfer, after run-1 | **USEFUL + COSTLY**: three fixtures run-101 -> natural run-3 (PROTO:219). "All four scans recorded zero partition calls" (PROTO:168, 219). After fix: alloc 48,576 -> 6,720-6,959 B per cleanup (COST:70); "R36 branch recorded zero activations through run-11" (COST:570-571). |
| R37 | Retire root `ZERO->DT` when every origin has a NORMAL witness | Recursive wrappers [REC] (CAT:169) | forward handoff, run-level stop | **USELESS** "in the copy-only scope" (PROTO:220). [A] prototype is "for closed copy-only root methods", requires `config.roots.singleOrNull()`, no generated blocks (`ARCH/implement-root-retirement.py`). Its own motivating fixtures (`RecursiveWrapper...`) are unchanged. |
| R38 | Same with complete possible-origin accounting, NoRoute | Phase-3/4 repair of R37 (CAT:1283-1286) | forward handoff | **USELESS** in the same scope (PROTO:221). |
| R39/R40 | Regular / nested field-word NoRoute certificates [REC][LOOP] | Branching and nested recursive writer/reader (CAT:1298-1322) | handoff | **Postponed**, unmeasured (PROTO:237; SPEC:42-45). |
| R41 | Retire a FLOW demand pair independently served by saved NORMAL replay | The real OWASP `doSomething` helper cycle (BASE:47-104; PERF:603-646) | handoff (+ run-level stop candidates) | **USEFUL + COSTLY** (PROTO:222). Geometry ablation: OWASP entry natural run-7 with both observations, global-cut run-7, root-MAY run-5. Closed-root variant: both synthetic cases run-7 but "retained the OWASP demand through run-101". Projects: geometry removed 7/8/5 origins at OWASP H4/H5/H6, H11 1,111 -> 1,002 pairs (PROTO:151-155); Conductor 71 origins at H2, 477,983 -> 477,877 pairs (PROTO:157-158); closed-root guard "made zero proof attempts at every completed handoff of the full project scans" (PROTO:194-195). |
| R42 | Uniform NORMAL MUST service replaces a covered cut DEMAND guide (handoff; live folding separate) | Global-cut and protected global-cut growth (CAT:662, 737); successor of R17/R24 | handoff (live variant: reply admission) | **USELESS** (PROTO:223): frontier 6 -> 3 at run-101, "The Target remained"; protected fixture still 7 pairs; "The selected compiled OWASP entry had no applicable candidate" (PROTO:322-323). Projects: skipped. |
| §8.1 singleton compaction, C5 entry reuse | Remove native work (not termination rules) | Rollback performance attribution | handoff, C5 | **USELESS for termination** (PROTO:224), projects skipped "under the termination-first gate". Singleton audit: zero singleton groups at H4 (PROTO:365-369). |
| §8.2 joined index seal | Rebuild saved-record indexes once per seal | Cost campaign | handoff | Not a rule; measured: rebuilds 202 -> 101 (COST:394), see §3. |
| §7.1 run-level candidates (observer census, closed run pair) | Driver stop when every reachable observer has a NORMAL receipt / when `S -> B -> S` repeats | Emerged in COST while trying to make R41 pay for itself | run-level, completed forward seal | Measured on the compiled OWASP entry and synthetic fixtures only (COST:256-375). |

Count check (current SPEC IDs R01-R42): USELESS 17 (R01, R02, R03, R04, R06, R07, R08, R10, R20, R27, R29, R31, R32, R34, R37, R38, R42); NATIVE/dependent 17 (R05, R09, R11, R12, R14, R15, R16, R18, R19, R21, R22, R23, R24, R25, R28, R30, R33); removed/postponed 3 (R17, R39, R40); USEFUL 5 (R13, R26, R35, R36, R41).

Eight fixtures changed from cutoff to natural stop (COST:22-24). [A] They are: exact-origin nested write (R13), uniform root cleaner (R26), descendant exact cleaner (R35), three nested cleaner cases (R36), global-cut growth and root-MAY renewal (R41).

---

## 2. The gap: why "useless" despite a proved counterexample

### 2.1 Structural fact that explains most of it

**[R]** TASK defines a four-phase loop: (1) find a termination counterexample "to the current approach" with "Keep all selected mechanisms enabled"; (2) fix it; (3) find a soundness loss the fix introduced; (4) fix that (TASK:17-27, 46-48). Phase 1 demands "Assume no hard iteration limit" (TASK:56).

**[R]** The catalogue therefore states each example as a counterexample *to the proposal stack at that time*, not to the native analyzer: "Counterexample to: NE by itself, with the original shallow C2/C5 policy" (CAT:582); "to bounded first-field refinement plus NORMAL precoverage" (CAT:664); "to solving the preceding cases with only neutral, unprotected FLOW uniform coverage" (CAT:739); "to NE, bounded primitive routing, same-lane uniform coverage and reply folding" (CAT:780); "to all preceding fixes while keeping the EXACT/FLOW write-keep exception" (CAT:873); "New required counterexample to the complete consolidated approach" (CAT:960).

**[R]** The stops were obtained in a reference model, not natively: "The production driver ... does not implement the complete reference protocol" (VALID:9); "Eleven examples were rechecked with their optional reply omissions withheld. In those cases, the existing R38 root Target rule is enough" (VALID:7).

**[I]** Consequence: a rule's "proved counterexample" proves that *the stack minus this rule* recurs in the model. It does not prove that *native plus this rule* terminates, on the fixture or anywhere. The prototype campaign tested exactly the latter ("Each prototype starts from that revision in a separate detached worktree", PROTO:5-6). The two experiments answer different questions, so a null result was the expected outcome for most rules. This is not one of the six candidate explanations; I add it as **(g) stack-relative rule: jointly necessary in the model, not sufficient alone on native**.

Direct evidence for (g) **[A]**: R07 changes zero of 92 case end states, including `ExcludedGuardCycleTest`, the native form of its own counterexample; R08 leaves `DeeperExcludedGuardCycleTest` at run-101; R37 leaves both `RecursiveWrapper` fixtures at run-101.

### 2.2 Count per explanation (primary cause; my classification [I])

| Explanation | Rules (primary) | n | Strongest evidence |
| --- | --- | ---: | --- |
| (g) stack-relative; renewal survives the rule alone | R01, R02, R03, R04, R06, R07, R08, R10 | 8 | R07 `"changed": []` [A]. PERF:570-571 on NE: "The nonempty tail improves the local cut geometry. The corresponding forward and backward demand keys still recur." PERF:616-617: "Increasing the global limit beyond those caps leaves the cuts unchanged" (the renewer is the relative cap `FL(Dp)+1`, which no R01-R10 rule touches). PROTO:283-284: the NE run-5 stop "depended on the missing C5 service". |
| (c) repair-of-repair (phase-4 soundness fix for a hole a proposal rule opened) | R20, R31, R32, R34, R38 | 5 | PROTO:213 R20 "required for the tested NE integration". AUDIT:121 "R31 repairs the cleaner case; R32 repairs run-2 same-head STAR relay" (holes in the R04 C2 split). CAT:1283 "R37 removes the sole root ZERO/DT permission ... Repaired by R38". These rules were never meant to stop anything; "useless for termination" is true by construction. |
| not a termination mechanism at all (ordering or invariant) | R27, R29 | 2 | AUDIT:144 proves R27 cannot change the result: "quiescent sound stores are order-independent". [A] both `"changed": []`. |
| (d) guards narrowed until it never applies | R37 | 1 | PROTO:220 "USELESS in the copy-only scope"; [A] prototype requires a single configured root, a copy-only root method and no generated blocks. Secondary for R38, R42-closed-root, and for the *useful* R26/R35/R41-closed-root on projects (below). |
| (e) fires, removes rows, demand is renewed anyway | R42 | 1 | PROTO:223 "reduced the global-cut frontier from 6 to 3 at run-101. The Target remained"; PROTO:328-329 "Even when it removes the three pairs, the surviving continuation can renew demand." |
| (a) trigger absent in real code | none as primary; secondary for R08, R42, and all five useful rules | 0 | PERF:231 "zero R08 overruns"; PROTO:322-323 R42 "no applicable candidate"; PROTO:168 R36 "partition counter remained zero on all four projects". |
| (b) existing mechanism already handles it | none of the 17 USELESS; this is the 17 NATIVE rules | 0 (+17) | PROTO:226-239. |
| (f) idealization (no run limit) | none as primary; applies to the whole campaign | 0 | see 2.3. |

Secondary effect worth stating separately: **five of the eight (g) rules are actively harmful in isolation** — R01-R03 (6 -> 302 pairs; lost confirmed observations in the first version), R04 (11 fixtures grow [A]), R06 (two natural run-5 stops become run-101 [A]), R10 (7 -> 240 pairs). They widen admission (more starts) without removing the renewer.

### 2.3 Cross-cutting explanations (a), (b), (f)

**(f) idealization.** [R] Production stops at run-11 by policy ("Keep the production run-11 policy and use run-101 in the termination suite", SPEC:50). [R] Three of four projects never reach it: Conductor times out in run-8, ThingsBoard hits the memory guard in run-1 with no completed engine, Stirling-PDF times out in run-11 (PROTO:44-47). [I] An uncapped-recurrence proof is about runs 5, 7, 9, ... of a tiny acyclic program; on the real projects the binding constraint is reached earlier and is a different quantity (heap in run-1, loop-boundary throughput). Even OWASP, which completes, loses nothing at the cutoff: 2,633 of 2,633 findings confirmed, zero provisional (PERF:32-34).

**(a) pattern absent.** [R] In the rule-test suite, 584 of 585 Java cases "stopped with no outgoing demand"; the one that reached run-11 is "the known LOOP Target renewal" (PERF:718-720, 753). [I] The CAT fixtures that were never stopped are three- and four-deep self-compositions of one helper with conditional mark rules inside it (`make(make(make(a)))` with `CM(p.f.g.g.M,T) => assign T to r.h.MUST`, CAT:203-214) or the "synthetic atomic core form" (CAT:874). I found no report that looks for these shapes in the four projects; the absence is suggested by fire counts of zero, not demonstrated.

**(b) already handled.** [R] 17 rules are native parity. [I] Notably the fixtures attributed to R15 and R19 are still `RUN_LIMIT` at run-101 natively (BASE:21-23), so "native parity" means the *rule text* is native, not that its counterexample is solved. Per VALID:7 those 11 fixtures stop in the reference only through R38.

### 2.4 The load-bearing rule was the one never really tested

**[I]** Joining VALID:13-38 with PROOFIDX: of the 24 in-scope catalogue entries, 11 (+ recursive wrappers) stop in the reference via root-Target retirement (R37/R38), 3 via cleaner rules (R26/R35/R36), 1 via R13, and the remaining 8 via the NE/child/uniform-coverage stack (R01-R12, R17/R24 -> R42). R37/R38 were moved to a deferred spec, prototyped only for a closed copy-only single root, and labelled USELESS there. So the rule responsible for about half of the reference stops has no meaningful native measurement, and its natural scope (loops, recursion) is explicitly postponed (SPEC:42-45).

---

## 3. What the evidence says does matter

### 3.1 For termination on real code: one mechanism, one entry point

- **R41 on the compiled OWASP helper** is the only rule tied to a real-code repetition. [R] Removing the six helper FLOW pairs at run-7 gives a natural stop at run-11 with both findings (BASE:85-91). The geometry ablation stops at run-7 (PROTO:347-359).
- [R] It is not sound as implemented: three run-5 replies exist natively and not under saved replay (COST:146-150); restoring them only at run-5 stops at run-9, restoring them always reaches run-101 (COST:168-183). "native_c2_not_monotone_under_reply_narrowing" is a Lean theorem (`UsefulRuleCosts.lean:219`): a `p.*/FLOW` demand admits coarse `p.MAY/T` and rejects precise `p.f.$/T` (COST:124-128).
- [R] The sound variant (closed root) does nothing on OWASP: the entry "supplies two roots" (PROTO:380-382), and makes zero attempts on all four projects (PROTO:194-195). The observer census cannot discharge it: 117 observer keys, 2 confirmed, 115 unconfirmed (COST:237-241).
- [R] Scale on the full project: the helper family is 72 of 776 H11 pairs (twelve `doSomething` owners, PERF:563-564); "The other 684 repeated pairs retain their exact keys ... Their complete dynamic guards remain open" (PERF:671-675); 20 are genuinely new exact points (PERF:543-553). [I] So even a perfect R41 leaves about 91% of the OWASP frontier and cannot produce a natural stop for the full scan.
- **Run-level closed run-pair stop** (not a numbered rule): [R] compiled OWASP entry stops at run-11 with `STOP_RULE`, both reports; driver 2.138 s vs 7.608 s to the run-101 cutoff (COST:343-356). Reservation 768 item visits + 54 field words (COST:369-372). Bounds: at most four roots, 64 joined actors, eight joined actors for the pair verifier (SPEC:1284-1288). [I] With 3,719-30,791 roots per project it is ineligible everywhere that matters.

### 3.2 For real project progress: the non-rule work removals

These are the only changes with measured, activation-backed effect on the four projects [R]:

- **Joined saved-record index seal**: index rebuilds 202 -> 101; record visits / output positions removed 2,526,160 / 2,620,205 (OWASP), 1,299,283 / 1,367,408 (Conductor), 2,023,128 / 2,052,209 (Stirling), 0 / 0 (ThingsBoard) (COST:394, 419-422). Conductor run-6 handoff 2.663 -> 1.368 s (COST:429-430); run-7 handoff 0.919 -> 0.579 s, kernel high-water 10.236 -> 9.980 GiB (COST:736-738).
- **Loop saved-DATA replay skip**: Stirling run-9 skipped 9,670,433 replays, 43,963,058 before the run-11 timeout; run-9 167.580 -> 141.997 s at equal offers (1,933,594 vs 1,933,064) and equal cuts (837,747) (COST:669-673). Conductor run-6 engine 489.9 -> 412.0 s (COST:797-800).
- **C5 index bypass for unique C2 keys**: 14,909 of 45,929 insertions on OWASP, compaction 0.289 -> 0.256 s (COST:585-588); 216,598 on Conductor, 215,127 of them in the run-2 handoff (COST:591-592); 133,135 on Stirling (COST:612).
- Prefix cut cache: 7,804 hits of 19,519 eligible, zero at the dominant owner (COST:899-903, 916-917). No demonstrated effect.

None changes any reached/completed/accepted checkpoint (COST:502-514, 674-675).

### 3.3 What actually blocks the projects (none is addressed by R01-R42)

- **ThingsBoard**: memory guard in run-1, 11,619,968,024 heap bytes (PROTO:114-116). Every rule in the spec acts from run-2 or at a handoff; R41 "exercise[s] neither R41 nor the compaction change" (COST:604-608).
- **Conductor**: run-8 timeout; run-6 does 25,204,141 loop boundary offers (COST:777); in the rolled-back build one owner, `WorkflowExecutorOps#decide`, had 1,147,748 boundary limit offers with zero cuts (PERF:188-190).
- **Stirling-PDF**: one loop owner, `decodeMimeHeader`: 6,389,744 boundary offers and 28,991,481 prepared C5 queries in run-9 (PROTO:181-182); run-11 timeout profile 46.26% loop restriction (COST:648-649).
- [I] All three are loop-boundary or run-1 volume problems. Loop and recursion rules are exactly what the spec postpones.

### 3.4 Why the rollback happened (rules that cost, not rules that help)

[R] R32 on shared static carry (Conductor run-2 OOM; PERF:8-15, 381-394); the qualified reply channel for possible starts (448,592 qualified memberships beside 449,452 ordinary, PERF:277-279; disabling it completes run-2 in 98.344 s, PERF:406-407); the revised loop observation bypassing the quantum C2 cache (`decide` C2 requests / cache hits 27,970 / 13,764 -> 1,061,221 / 0, PERF:208) and requesting "a complete observation for each attempted prefix" (PERF:496-498; Stirling run-3 4.224 -> 418.955 s, PERF:93). [I] These map to R32, R06/R09-R12, and R20/R21 — all in the USELESS or dependent classes.

### 3.5 Remaining costs of the five useful rules after 20261119

| Rule | Residual cost / open item |
| --- | --- |
| R13 | Three builds lost two Stirling iterations; attribution open ("A single macro sample cannot show whether an isolated transfer change causes one shape to replace another", COST:833-835). Conductor run-6 RSS median 9.938 vs 9.683 GiB with post-pause heap 5,381 vs 5,397 MiB (COST:778-779), i.e. not retained heap. Changes results: 66 of 216 nested-write forms change stop or report metadata (COST:44-50). |
| R26, R35 | Inactive on all projects; structural checks 32 -> 1; no residual measured cost. Semantic cost: accepted precision loss (CAT:732-734). "No higher-heap completion result for this prototype yet" (COST:532-533). |
| R36 | Zero activations on all projects; "Its higher Conductor RSS remains an attribution question" (10.392 vs 9.944 GiB with post-pause heap 7,304 vs 7,307 MiB, COST:578-582). One ThingsBoard prescan exception, not reproduced (COST:558-566). "R36 is restricted to runs after run-1." |
| R41 | Soundness: continuation proof open (COST:124-137, 511-512). Budget: fixed 12,000-step diagnostic quota vs six skipped insertions of allowance (COST:117-122); zero singleton groups at the discharging handoff (PROTO:365-369). Sound variant ineligible on every project. |

---

## 4. Blind spots and weakly supported verdicts

### 4.1 Not measured

1. **No project runs for any USELESS rule** ("Skipped", PROTO:205-224) and **no activation counts** for them anywhere. "Never fires on real code" is supported by counters only for R08 (one Conductor run of the full build), R36, and the R26/R35/R41 guards.
2. **No combinations.** Rules designed as a stack were tested one at a time, except R01-R03+R20 and the union of the five useful ones. The stack that the 24 reference stops rely on (NE + children + uniform coverage + R38) was measured only as the full rolled-back implementation, which also carried R32 and the qualified channel.
3. **R37/R38 outside a copy-only single root; R39/R40 at all.** Recursion and loop fixtures remain at run-101 or timeout (BASE:27-30).
4. **Live R42 reply folding** (the variant that would prevent work rather than trim the handoff) — spec-only (PROTO:341-345).
5. **One real entry point.** All "real" termination evidence is `BenchmarkTest01000#doPost` / `Test#doSomething`. No census of which CAT patterns occur in Conductor, ThingsBoard or Stirling, and no run-101 for any full project.
6. **Soundness value.** The single decision criterion is a natural stop (PROTO:11-12). R31, R32, R34 are soundness repairs; R34 recovers observations the native analyzer loses (PROTO:216), R13 removes a spurious provisional report. "USELESS" hides that.
7. **The 684 repeated OWASP pairs** that are not the helper family, and the loop Target callbacks (433,878 at run-11, PERF:677-680).
8. **Higher budgets.** Three projects are cut by heap or timeout before most rules could act; no run with a larger heap or timeout exists (COST:531-533).
9. **Matched repeats** required by SPEC §8.4 ("repeated interleaved native and candidate scans") were done only ad hoc.

### 4.2 Weakly supported verdicts

- **Every COSTLY label.** [R] Each rests on one RSS sample of +0.15 to +0.56 GiB while the rule's guard was inactive (R26, R35, R36 zero activations; R41 closed root zero attempts). Native-to-native Conductor peaks: 9.749, 9.944, 10.145, 10.236 GiB (PROTO:45, 61; COST:454, 725-726). The report itself says "That control variation is larger than several measured prototype deltas" (PROTO:191-192). [I] COSTLY should read "unmeasured, within noise".
- **Anything on Stirling-PDF.** [R] Run-9 engine time on unchanged or irrelevant builds: 725.199, 390.653, 4.450 s (PROTO:177); boundary offers 6,389,744 / 4,375,223 / 38,074. The "R36 completes run-11 in 152.859 s with two more locations" result occurred with zero activations (PROTO:168-173). [I] The native engine is multi-modal on this project by about 160x; that nondeterminism is a larger finding than any rule delta and invalidates single-sample comparisons, including "R13 lost two iterations".
- **Fixture noise in the termination suite.** [A] `globalCutGrowth` ends run-101 with 4 pairs instead of 6 in at least 13 prototypes that cannot plausibly affect it (C5-SHARE, R20, R31, R34, R37, R42-shadow, R13 and R35 variants), and with 6 in others (R07, R27, R29, R36, SINGLETON). The timeout fixture flips between run-20, 21 and 22. [I] So "R42 reduced the frontier from 6 to 3" and "R10 7 instead of 6" are within one unexplained 6-vs-4 baseline wobble; the PROTO text does not mention it.
- **PROTO understates harm for R04 and R06.** PROTO:206 cites one fixture "from 4 to 7"; [A] eleven grew, alternating to 9. PROTO:207 cites "One deferred recursive control"; [A] eight changed, two to the run-101 cutoff.
- **R41 project effect.** OWASP H11 "1,111 -> 1,002" (PROTO:153) is inside the unrelated spread: native 1,111 and 1,153, R13 and inactive-R26 builds 975 (COST:517-522: "The handoff count alone does not attribute the drop").
- **R13 "useful".** Its fixture is a synthetic core form with no JVM lowering claim (CAT:874-875); it stops because it deletes a spurious fact. Zero evidence that the strict-child keep fires on any project.
- **R01-R03 "useless".** True for the corrected version, but the corrected version is NE + R20 only, without R05/R09/R21/R23, which PROTO:230 says cannot be driven without NE. The NE family was never tested as designed short of the full implementation.

### 4.3 Bottom line [I]

The campaign optimised for "does the model with all rules stop on a 10-line acyclic program with no run limit". Real workloads fail on a different axis (run-1 heap, loop-boundary volume, a 3-8 run budget). The rules are mostly correct answers to a question the production analyzer is not being asked; the handful with real traction are R41 (one helper shape, soundness open) and three pieces of plain work removal that are not rules.
