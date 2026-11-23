# Acyclic convergence for the bidirectional analyzer

Status: PROPOSAL, 23 November 2026. Condensed from
[natural-termination-proposal.md](natural-termination-proposal.md) §5.
All rules below are native prototypes behind flags on local branches.
None is merged. It follows the [design guide](design-guide.md).

## 1. Requirement

**Assumption.** JVM pass rules have no `[any]` in `from` or `to`. Source
and sink conditions with `[any]`, and conjunctions, are allowed. They make
MAY facts in backward runs only.

**Definition.** A method is *acyclic* when it has no loop and no method
that it reaches through resolved calls is recursive or has a loop. A
model without a body is a leaf; an analysed approximation body is code.
A block is acyclic when its method has no loop before it and it reaches
no cyclic method.

**Requirement AC.** For each acyclic method or block there is a forward
run after which it has no row in any forward handoff. The callers do not
matter: if a method has no demand row, a caller's demand gets no C2
start there, and the caller replays the method's complete records. The
caller's own rows carry the caller's imprecision. No stop test and no
limit may give AC. The analysis itself must converge.

**Why it must be possible.** In acyclic code every access path has a
bounded depth. When K is larger than that depth, no global cut happens.
Then every remaining DEMAND row comes from a maker that does not read K.
Under the assumption, every such maker is made by the analyzer, so each
one can be removed at its source.

**Gate.** Confirmed and provisional results must be identical to native,
by SARIF identity and code flows, on every project and suite. A change
that looks like a precision gain is a failure, because there is no
trusted ground truth. Time and peak memory must not be worse.

## 2. Makers of acyclic demand

Measured with a shadow census on OWASP, Stirling-PDF, Conductor, the rule
suite and the module suite (branch `proto/acyclic-census-20261120`).
Natively 350 acyclic OWASP owners never reach zero rows (164 `doPost`,
164 `doGet`, 22 `doSomething`), about two thirds of OWASP's open demand.

| Maker | Where it shows | Fix | Status |
| --- | --- | --- | --- |
| DemandTarget renewal at a sink with a complete ZERO target | 919 forward rows at 431 OWASP roots, in a closed two-run cycle with no DATA row | X (§3.3), needs the G6 drop form (§3.2) | Selected |
| The same, relayed into a caller with a complete target | `bytesToWebResponse` loop on Stirling-PDF: anchors 38 of 43 acyclic rows | RX (§3.4) | Selected |
| A DEMAND callee reply that a NORMAL MUST reply covers | OWASP `doSomething` families | MUST-cover (§3.1) | Selected |
| Cleaner survivor: an EXACT cleaner at a point of a MUST region | DemandTarget witnesses at 151 of 164 OWASP roots; `Thing2` | MUST ignores an EXACT cleaner (§3.5) | Selected |
| Relative C5 cap `FL(Dp)+1` in acyclic methods | OWASP helpers; Stirling-PDF | No cap in acyclic methods (§3.6) | Selected |
| Relative C5 cap at an acyclic block exit | `decodeMimeHeader` block 1 | C5B (§3.7) | Candidate |
| Read at a strict prefix of a premise ("inside read") | OWASP `new String(byte[])` helpers; Stirling-PDF `saveUser` | — | Open (§5) |
| STAR start from a backward MAY row | Stirling-PDF `bytesToWebResponse` STAR arms, `AuthController#login` | — | Open (§5) |
| Complete backward-ZERO and ND rows | 730 backward rows on OWASP | — | Not a driver: they follow the DemandTarget cycle |

## 3. Selected rules

### 3.1 MUST-cover reply rule

Flags `-Dorg.opentaint.bidi.mustCoveredReply=true`,
`mustCoveredAcyclicOnly=true`. Branch `proto/dosomething-fix-20261120`.

- **Cause.** A caller offers `arg(1).MUST/T`. Saved replay returns the
  NORMAL reply `ret.MUST/T` first (`engine/RunMethodCallServices.kt:347`).
  The subscription also applies the callee's current DEMAND replies
  (`:393-409`). The layer is part of the group key
  (`ap/Conclusions.kt:69-71`), so the MUST fact never covers the MAY fact.
  The MAY fact reaches the sink and renews a DemandTarget.
- **Rule.** In forward restricted runs, drop a current DEMAND callee reply
  when a NORMAL MUST leaf that saved replay resumed for the same caller
  premise and call point covers every leaf (same base and mark, MUST path
  a prefix, exclusion admits the rest). Protected facts are kept. Only
  for callees whose call cone is acyclic.
- **Exactness.** Within a run no NORMAL fact, record, target or report
  changes. Across runs it is not exact: on one OWASP entry native adds 6
  records and 4 block targets that the rule never makes. No report
  changes.
- **Gate.** Module suite 340 of 342 identical (2 acyclic fixtures stop
  earlier, same report); rule suite identical; OWASP 7 launches identical;
  the 5 `doSomething` families have 0 rows from H5. Without the acyclic
  scope Conductor's H7 rows double, so the scope is required.

### 3.2 G6 drop form (prerequisite of §3.3 and §3.4)

Flag `-Dorg.opentaint.bidi.g6Drop=true`. Branch `proto/g6-drop-xsub-20261120`.
Decision of 20 November.

- **Defect.** The type filter's primitive-tracking mark policy read only
  the root and the element spine of a value (`ap/Filter.kt:97-139`,
  `JIRTypeFilters.kt:48-56`). A cut MAY tail at a boxed level (`Integer`,
  `Long`, `Boolean`, `Character`, also as array elements) lost an
  ordinary mark, while the exact fact under `value` kept it. So a small K
  reached fewer sinks than a large K, and the native analysis also lost a
  finding when the boxed value came out of a callee.
- **Rule.** At a boxed level, drop a non-primitive-tracking mark on the
  whole value, including the leaves below it. True primitive levels and
  primitive-tracking marks keep the native behaviour.
- **Gate.** Prefix-closed over 29 real JIR types and 1,464 paths: 0 cut
  facts dropped while the exact fact is kept (native 1,114). It removes
  finding B in the synthetic fixtures M4, D5, D6 and 13 boxed string
  chains, at every K. Rule suite and all three projects identical; on
  OWASP it never acts.

### 3.3 DemandTarget subsumption X

Flag `-Dorg.opentaint.bidi.dtSubsumption=true`. Branch
`proto/dt-subsumption-20261120`.

- **Rule.** At a forward sink witness, a DEMAND arm emits no DemandTarget
  and captures no seed when the same method and block scope already has a
  complete ZERO → NormalTarget for the same sink (saved, or emitted earlier
  in the run).
- **Exactness argument.** ZERO is the weakest premise, so the complete
  target covers every premise of the DemandTarget for this sink at this
  owner. The decision is per sink witness. It reads a complete summary of
  the owner, not the report sets. It is correct only when every sink that
  a later run can confirm keeps its own witness and seed, so it needs the
  G6 drop form: without it, 17 module analyses lose finding B.
- **Gate (with the G6 drop form).** Module suite 0 report changes; rule
  suite identical; OWASP 3 + 3 + 3 launches identical; forward rows of
  loop-free OWASP owners 711-753 → 39-63, no Target row from H5.

### 3.4 Relay subsumption RX

Branch `proto/stirling-ac-20261121`.

- **Rule.** A witness tags its DemandTarget with its report identity. A
  tagged DemandTarget is not relayed into a caller that already has a
  complete ZERO → NormalTarget for that identity.
- **Exactness argument.** The same as X, at the caller.
- **Why not a wider cover.** Covering a DEMAND arm with an ND premise by a
  complete target whose premise is a subset loses `B@g:1` in fixture M3:
  that arm's DemandTarget and seed are the only refinement channel for
  callers that bind the premise on the DEMAND layer.
- **Gate (on S, §4).** Stirling-PDF: acyclic residual 43 → 19, end
  `FIXED_POINT` 33 → 15, driver 577-581 s → 71-72 s, same report. OWASP:
  forward rows 99 → 11, residual 6 → 2. Conductor: residual 15 → 11.
  Rule suite identical. Module suite: 325 analyses identical. The tag
  breaks 49 unit assertions that compare the untagged DemandTarget object
  or count DemandTarget rows.

### 3.5 An EXACT cleaner does not apply to a MUST fact

Flag `-Dorg.opentaint.bidi.mustIgnoresExactCleaner=true`. Branch
`proto/must-cleaner-20261121`. Decision of 21 November.

- **Cause.** After an EXACT cleaner at `c` on `x.MUST`, the strict
  descendants of `c` have no NORMAL form. Natively the whole region
  becomes DEMAND (`ap/Clean.kt:194-218`).
- **Rule.** When the reach is EXACT, the leaf is a MUST (`ANY_TAINT`)
  leaf and its region holds the point, the leaf stays unchanged: same
  layer, marks, exclusion and protection (`ap/Clean.kt:202, 230-240`;
  reference model `ap/Reference.kt:491-493`). Exact `$` marks, MAY and
  STAR leaves, FLOW facts and BELOW / AT_AND_BELOW cleaners keep the
  native behaviour. It is a precision trade: the cleaned point stays
  tainted inside a MUST region.
- **On real code** it fired 91-3,491 times per launch, always on the MUST
  leaf at the cleaned root of `ret`, `<this>` or `arg(0)` (`toString()`,
  `HtmlUtils.htmlEscape`, `prepareStatement`), never in a backward run.
- **Gate.** Projects and rule suite identical (0 FN, 0 FP). Module suite:
  1 new confirmed finding (`UniformRootCleanerTerminationTest`, the
  designed trade) and 3 provisional → confirmed. These 4 fixture changes
  need sign-off under the gate rule of §1.

### 3.6 No relative C5 cap in acyclic methods

Flag `acC5Exact`. Branch `proto/ac-closure-20261121`.

- **Rule.** An acyclic method publishes its C5 output without the
  relative cap `FL(Dp)+1` (the global cut still applies).
- **Gate.** No report change. It adds no facts: acyclic NORMAL facts fall
  by 1.0 % (OWASP), 0.1 % (Stirling-PDF), 1.1 % (Conductor). Without it
  the residual rises (OWASP 6 → 18).

### 3.7 Candidate: no relative cap at acyclic block exits (C5B)

`decodeMimeHeader` block rows 8 → 2, same reports, +1.7 % driver time on
Stirling-PDF (2 launches). Not selected while it costs time.

## 4. Combined result

Measured on the stack of the main proposal (canonical order,
`FIXED_POINT`, the cycle fold W). Configuration S = that stack + §3.1,
§3.2, §3.3, §3.5, §3.6. Forward AC residual = forward handoff rows of
acyclic owners at the last forward barrier.

| Stage | OWASP | Stirling-PDF | Conductor (H7) | Rule suite | Module suite (analyses / rows) |
| --- | --- | --- | --- | --- | --- |
| Native | 711-753 | — | — | — | — |
| + §3.1, §3.2, §3.3 | 33 | 47 | 21 | 8 | 21 / 56 |
| S (+ §3.5, §3.6) | 6 | 43 | 15 | 8 | 18 / 47 |
| S + RX (§3.4) | 2 | 19 | 11 | 8 | — |

- Reports: identical to native on all three projects and the rule suite
  in every stage. Module-suite changes: the §3.2 removals in synthetic
  fixtures and the four §3.5 fixture changes.
- OWASP with S: `FIXED_POINT` at run-11, driver 105 s against 132-134 s
  native (census off). Stirling-PDF with S + RX: `FIXED_POINT` at run-15,
  driver 71-72 s. Conductor: still a timeout (cyclic growth, main
  proposal §6).

## 5. What remains

1. **Inside reads.** The `new String(byte[])` model edge on the coarse
   premise `arg(1).String#bytes.*` gives a DEMAND reply `ret.MAY` that
   reaches exact actuals `String#bytes.$`, although an exact `$` holds no
   array element. Two rules removed it at the source: "start the finer
   premise in the same run" and "mark the reply unrefinable". Both
   empty OWASP's demand (`NO_DEMAND_EDGE` at run-7). Both fail the gate
   on Stirling-PDF: they remove the two provisional stored-XSS results
   `UserController.java:753` and `:768`. These results exist only
   because the reply's demand rows in `UserService#saveUser` make a coarse
   backward row (`REPO.MAY/XSS => ZERO`) that restarts the controllers in
   every later run. For this maker, AC and identical provisional output
   cannot both hold. Decision needed:
   - accept the loss (contradicts the gate rule);
   - an explicit AC exception for demand on which native provisional
     output depends;
   - keep the results through another channel (would carry reached sets
     across runs; on OWASP it would add about 500 provisional results).
2. **STAR start from a backward MAY row.** A backward MAY row (from a
   reversed MAY rule edge or an any-field sink seed) admits a forward STAR
   start that is DEMAND by itself. It keeps `bytesToWebResponse` (14 rows)
   and `AuthController#login` (3 rows) open on Stirling-PDF. No exact
   cover was found. This is the next maker to study.
3. **Module fixtures.** 4 rows from an intrinsic MAY rule (outside the
   assumption) and a few others.
4. **Rule case 349.** 8 Target rows in a block of
   `UnsafeFileUploadServlet#doPost` that no loop precedes. Not traced.

## 6. Rejected after test

| Rule | Why |
| --- | --- |
| Offer closure: no start for a DEMAND offer that the callee's record covers | Loses `delayed U sink`: the callee row is also the C2 admission key for later refined offers |
| Exact start: start a deep actual at its full depth | Refines deeper than requested; facts in affected callees +20-60 % |
| Excluded-point exclusion member ε for cleaned MUST regions | Replaced by §3.5, which needs no new representation |
| Do not hand off a complete row already served | Loses findings: with a larger K the same row is a different input |
| Persist backward ZERO rows as admission rules | Loses M3: the backward run no longer reopens the seed path |
| G6 guard (no stop while boxed drops happen) | Conductor drops in every run, so X never acts there |
| G6 keep form (keep MAY-tail marks at boxed levels) | Not selected; the drop form matches the policy's intent |
| Inside-read rule; unrefinable MAY (option A) | Remove two native provisional results on Stirling-PDF (§5.1) |
| DemandTarget relay with a call-site seed (ND cover) | Exact but 3 min against 3.4 s in one forward run |

## 7. Semantic scope

Changed: the C5 publication of acyclic methods (§3.6); the reply set at a
call for acyclic callees (§3.1); the primitive-tracking mark policy
(§3.2); DemandTarget emission, seed capture and relay at sinks with a
complete ZERO target (§3.3, §3.4), including a report identity on the
DemandTarget; the cleaner on MUST leaves (§3.5).

Unchanged: the stop rules, field transfer outside these sites, C2, the
handoff projection and compaction, run-1 and run-2 static views, the
field-limit schedule, the report rules.

## 8. Implementation and gate plan

1. Land each rule behind its flag on the current branch, in this order:
   §3.2, §3.3, §3.4, §3.1, §3.6, §3.5. Each depends only on the rules
   before it (§3.3 needs §3.2).
2. Gate each rule alone against native: module suite, jvm suite, rule
   suite, OWASP 3 interleaved launches per arm, Stirling-PDF 2, Conductor
   1. Reports identical (except the signed-off changes), time and memory
   not worse. So far the rules were gated on the stack of the main
   proposal, not alone against native.
3. Gate the combination, with the census on, and report the forward AC
   residual per project.
4. Update the unit expectations that check the old representation (the
   RX tag, cleaner tables, the G6 tests).

## 9. Proof scope and blind spots

- No rule has a proof. The exactness arguments above are code readings
  checked by native fixtures and gates.
- X and RX rely on "every later-confirmable sink keeps its own witness and
  seed", which needs the analysis to be monotone in K. The G6 drop form
  removes the one known non-monotone filter. Loops are not monotone
  natively (`LoopOutputRestriction.restrictScalar`), but loops are outside
  AC.
- Project gates are 1-3 launches per arm on a shared host.
- ThingsBoard was not run (it fails in run-1 for memory).
