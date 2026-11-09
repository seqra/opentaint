# Guidelines for this investigation

These are the working rules for the fact-explosion work. They come from the errors that cost the
most time. Read them before you start a new cycle.

Write in ASD-STE100 Simplified Technical English. This document uses that style.

---

## 1. The pipeline

Do the steps in this order. Do not skip a step.

1. **Write the spec. Prove the invariants.** Use a CEGAR loop to correct the spec.
2. **Make a small repro. Verify the implementation on it.**
3. **If you have a proof AND evidence from the repro, run the real project.**
4. **If the result is not sufficient, go back to step 1.**

A negative result at step 2 is a success of the method. It stops you from building the wrong thing.
Record it and go back to step 1.

---

## 2. The formal spec

### 2.1 Model first, measure second

A question about STRUCTURE is not an empirical question. If you ask "can this walk emit more than
N items", prove it. A measurement tells you about one project. A proof tells you about all inputs.

Measure to CORROBORATE a proof, or to find the shape of a workload. Do not measure to decide a
question that the model can answer.

### 2.2 Only constructive proofs

* No classical axioms. `propext` and `Quot.sound` are permitted. `Classical.choice` is not.
* Every existence proof must give an executable witness. Write the witness as a function and
  `#eval` it.
* Do not use `native_decide`. It adds an axiom.

**Always audit.** After each module, run `#print axioms` on every theorem. Do not trust the build.

```
#print axioms my_theorem
```

**Known sources of `Classical.choice`:**

| Source | Use instead |
|---|---|
| `beq_self_eq_true` | prove reflexivity by recursion (`Nat.beq n n = true`) |
| bare `simp` | `simp only [...]` with named lemmas, or `rw` |
| `List.any_eq_true` with `obtain` | induction on the list |

### 2.3 Prove the direction that matters

The strict requirement is: **the change can never cause a false negative, in any scenario.**

* State soundness as "everything the old form answered, the new form answers".
* An over-approximation is safe. A drop is not.
* **A prefix is not automatically more general.** `x.f` and `x.f.g` are incomparable as exact
  patterns. To generalise a path you must add a wildcard: `prefix.[any]`.
* Beware of "registration, not matching": a wildcard fact can answer LESS than a concrete one. No
  reader flag repairs that. Prove the EMISSION-side statement, not only the denotation.

### 2.4 Separate the concept from the optimisation

Prove two things:

1. They are functionally equal (or the optimisation only adds).
2. They have different complexity, at least over a practical scope.

State the complexity as a closed form when you can. `n * (k + 2)` against `n + k + 1` is a product
against a sum, and that is the useful statement.

### 2.5 Use the model to find bugs

The model earns its cost when it refuses a design. Examples from this work:

* `the_naive_reader_loses` found a false negative in the context cap BEFORE the code existed.
* `rung_is_monotone` found a missing hypothesis (`f <= c`) in my own statement.
* `concurrent_can_exceed` showed that a safe concurrent READ does not give a hard bound.
* `the_guard_is_load_bearing` showed that one code guard changes a bound from linear to exponential.

When a proof fails, read the goal. It usually names the missing condition.

### 2.6 Keep the joins honest

If two modules use different carriers, the chain between them is a CORRESPONDENCE, not one theorem.
Say so. Do not quote a chain of modules as if it were machine-checked end to end.

---

## 3. Language

Use ASD-STE100 Simplified Technical English.

* One idea in one sentence.
* Use the active voice. Write "the cap bounds the population", not "the population is bounded".
* Use short sentences. Twenty words or fewer for a procedure.
* Use one word for one meaning. Do not change "premise" to "demand" to "requirement" in one
  paragraph.
* Do not use idioms, metaphors, or humour.
* Use approved technical terms. Define a term once, then keep it.
* Write numbers with their units and their COUNTER NAME. See section 4.1.

---

## 4. Measurement discipline

### 4.1 Name the counter in the number

"1.4M events" and "4.67M events" were `factAdd` and `Progress`. They are different counters. That
mistake produced a false "two regimes" conclusion and sent the work in the wrong direction.

**Always write the counter name with the number.**

### 4.2 A run is not a pass because it did not OOM

The verdict must require ALL of:

* two `Analysis done in` lines (conductor has two units);
* zero `Running low on memory`;
* zero `Got exception`;
* no `status=TIMEOUT` and no `status=EXCEPTION`.

A unit writes `Analysis done in` AFTER it throws. A timeout sets neither the guard nor a low `done`
count. Three arms in one session reported `done=2 oom=0` and had all failed.

### 4.3 Each failure mode hides the others

* An **exception** hides an OOM: the run stops before the heap fills.
* A **timeout** hides an OOM: the run stops before the heap fills.
* Therefore "no OOM" under a tight time budget is NOT evidence of bounded memory. Re-measure at a
  much larger budget before you claim memory is solved.

### 4.4 Probe the mechanism before you build the fix

Build a cheap, even unsound, probe that tests whether the mechanism you believe in is the driver. If
capping X removes nothing, do not build a careful sound version of capping X.

One probe of two arms and six minutes replaced a large encoding that would not have helped.

### 4.5 Judge on both axes

Fact bounds move cost to premises. A win on `factAdd` alone means nothing. Report `factAdd` AND
`premisePair` for every arm. The same rule applies to memory and time.

### 4.6 Check that the operator fires

Read the liveness counter before you read any timing. An operator that ships off, or that never
matches, produces a timing that means nothing.

Example: `selfTrimAgainstOwnAny` was asked 3,209,211 times and matched zero.

### 4.7 Never judge a flag from a bundled arm

If an arm sets three flags, you learn about the bundle. Measure the flag alone before you conclude
anything about it.

### 4.8 Profile correctly

* A handful of stack samples is not a profile. Take hundreds.
* **Check the queue depth first.** If the work queue is empty, most threads are parked. A frame can
  dominate the RUNNABLE threads and still be a small part of wall-clock time.
* Rank frames by share of wall-clock, not by share of the threads that are awake.
* Confirm a profile-driven change by measurement. One change that looked decisive gave 2%. Another
  avoided 1.33 billion calls and gave nothing.

### 4.9 How to census the heap (three traps, all hit in one session)

1. **`jmap -histo` and `jmap -histo:live` BOTH force a full GC.** The fact store is behind
   `SoftReference`, so the forced collection clears exactly what you are measuring. Both reported
   about 13,000 `AccessNode`; the truth was 74.9 million. Use:
   ```
   jcmd <pid> GC.class_histogram -all
   ```
2. **The log's `Memory usage:` line is `maxMemory - freeMemory()` -- it counts garbage.** A census
   triggered at "79%" of that metric runs at about 4.5 GB LIVE, long before the wall, and the answer
   comes out "the heap is the IR". Trigger the census on the ABSOLUTE size you care about, or take
   it from a larger-heap run at the size where the small-heap run dies.
3. **Confirm retention with the GC log.** `-Xlog:gc` and read the `Pause Full` lines. If they say
   `7378M->7378M(8192M)`, the memory is live and no allocation-side change will help.

Give a harness NO analysis flags of its own, and make it print the finding SET (rule, file, line),
not a count. A count cannot show WHICH finding was lost, and a harness with flags is a bundled arm.

### 4.10 Run the RECALL GATE before you believe any finding count

A project's finding count can be insensitive to the thing you changed. Conductor's four reference
findings are CONCRETE flows, so an arm that loses STARRED (`[any]`) flows still reports 4 of 4. Two
arms were published as "the exact reference finding set" and were then shown to lose 14 unit-test
findings.

The gate costs about a minute:

```
./gradlew --no-daemon cleanTest test --tests 'org.opentaint.jvm.sast.dataflow.*AnalysisTest' -D<arm flags>
```

* `build.gradle.kts` forwards every `-Dopentaint.*` to the test JVM.
* **`cleanTest` is required.** Without it Gradle reports the task up to date and you read the
  PREVIOUS arm's results, which look like a pass.
* The baseline has 5 failures in `HarnessSmokeAnalysisTest` from a missing fixture. Subtract them.
* **Read the messages, do not count them.** The single discriminator is `fwd=`:
  * `fwd=0`, or `expected taint to reach the sink, but no vulnerability was found` -- a LOST
    finding. This is the only kind that matters.
  * `fwd=1` -- the finding is KEPT. The test is asserting something about CONVERGENCE ("the repro
    must still explode", "depth 2 must reach the fixed point", "the control must converge"), and it
    fails because the arm changed how far an internal arm gets. That is a performance statement, not
    a recall one.

  Counting failures instead of reading them made an arm with ZERO losses look like it lost five.

Run this gate on every arm before it goes in a claim.

### 4.11 The forward scan gets 80% of the IFDS timeout

`TaintAnalyzer.runAdaptiveEpochs` grants the epoch
`(ifdsTimeout - elapsedSoFar) * 0.80`. With `--ifds-analysis-timeout=500` that is about **373 s**,
and the log states it: `Full scan epoch 0: ... budget=6m 13.5s`.

So an arm "measured at 500 s" is a 373 s forward scan, and `Ifds analysis timeout` fires at that
mark, not at the number you passed. Read the `budget=` line before drawing any conclusion about how
much time an arm was given.

### 4.12 Repeat an arm before you claim a difference

The run-to-run spread on conductor is about **30% in progress**. A single run of arm A beating a
single run of arm B says almost nothing.

Worse: an arm whose SCHEDULING is not deterministic can report a different FINDING SET each time. A
per-unit resume was measured at 4, 3 and 3 findings over three identical runs, because thread timing
decides which units get ahead and a truncated run then explores different parts of the program.

* Run every candidate at least three times before you compare it with anything.
* If the finding set varies between runs, the arm is not shippable whatever its speed. For a
  security analyser a nondeterministic finding set is worse than a slow one.
* Report the SPREAD, not just the best run.

### 4.13 Compare progress at cutoff, not elapsed time

When every arm stops at the same timeout, elapsed time is the same by construction. Compare the work
done at the cutoff.

---

## 5. Lean notes

These cost real time. Lean 4.33.1, no Mathlib.

* **A doc comment `/-- ... -/` before `mutual` does not parse.** Use a line comment `--`. This error
  cascades and hides every later error in the file. It occurred three times.
* `set_option ... in` must come BEFORE the doc comment of the declaration.
* `split_ifs` is a Mathlib tactic. In core, use `split`, or `cases h : cond`.
* `cases h : e` substitutes in the GOAL only. It does not rewrite existing hypotheses. A later
  `rw [h] at h' ⊢` then fails on the goal.
* `if false = true then a else b` does not reduce for `exact`. Use `cond`, then `show` and `have` to
  force the reduction, or name the reduction lemma.
* `rfl` fails on a function defined by well-founded recursion. Use the equation lemmas.
* `ring` is not available. Use `omega`, and give it the products as explicit `have` equations.
  `omega` cannot do non-linear arithmetic; `m * (k + 2)` is an opaque atom to it.
* `decide` reaches the recursion limit on lists of moderate size. Raise `maxRecDepth`, or state the
  closed form and prove it by induction so the result does not depend on what `decide` can reach.
* Prove a general closed form when you can. A `decide` table is tied to the sizes it can compute.

---

## 6. Shell and process notes

* **`pkill -f <pattern>` matches your own shell.** The pattern appears in your command line, so you
  kill yourself. Use:
  ```
  ps -eo pid,comm,args --no-headers | awk '$2=="java" && /marker/{print $1}'
  ```
  The `comm` test excludes your shell.
* A foreground `sleep` is blocked. Poll in a bounded loop.
* Traces fill the disk. Cap the trace, and check that the drop counter is zero before you use the
  data. A truncated field also invalidates any count that splits on it.
* Give each arm its own output directory and write a machine-readable verdict file.

---

## 7. Repository notes

* Build the analyser with `./gradlew projectAnalyzerJar` from `core/`.
* A bare `gradlew test` in `core/` skips the included build `opentaint-dataflow-core`. Name the
  module.
* `rules/` contains a copy of itself. Check the rule count in the log before you trust an arm.
* Copy the jar to a per-experiment path. Do not let two arms share one jar file.

---

## 8. How to write a claim

Every claim in `CLAIMS.md` needs:

* a **status**: PROVED, MEASURED, ASSUMED, or REFUTED;
* for PROVED: the module, the theorem names, and the axiom audit result;
* for MEASURED: the flags in force, the counter names, and the arm names;
* the numbers in a table;
* what the claim does NOT cover.

Correct a claim in place, and keep the correction visible. A claim that was wrong is more useful
with its correction than deleted, because it stops the same error a second time.

Add a claim when you refute something. A refutation is a result.

## 4.13 Normalise every census count, and score a fact operator on TWO counters

A census count is proportional to the work the arm did. Two arms at the same wall-clock budget do NOT
process the same number of events, so a raw count compares throughput, not shape. **Divide by
processed events before comparing arms.** Claim 86 was hidden for one whole round because the raw
per-tree number said the opposite of the per-event number.

Then score the operator on both of these, because they can move in opposite directions:

* `AdaptiveWorkload` -- fact **ADDS**, what the run STORES;
* `FactShapeCensus` -- trees **OFFERED**, what the run BUILDS.

The recommended arm stores x0.31 and builds x21.7 per stored fact (Claim 87). One counter alone
ranks it best; the other alone ranks it worst. An operator that shrinks trees will raise construction
churn, and the churn is what a bigger heap cannot buy back.

Also check that a size-triggered mechanism has not switched itself off: `MIN_SIZE_TO_INTERN` is 100
nodes and the bounded arm's mean tree is 6.35, so its interner never runs.

## 4.14 Score the memory gate ONLY on solo runs, and never read `oom=0` as "memory is solved"

The harness scores an arm on whichever wall it hits first, and the two walls are not independent.
Across eight full-budget conductor runs, every run that ended at 368-384 s OOMed and every run that
reached 470-496 s reported TIMEOUT (Claim 91). A run that goes fast reaches the heap limit and is
scored OOM; the SAME configuration under CPU contention crawls, never reaches the limit, and is
scored a clean TIMEOUT.

So:

* **`oom=0` on a timed-out run carries no memory information.** It usually means the run was too slow
  to run out. Quote it only together with the event count and the elapsed time.
* **Run gate arms ONE AT A TIME.** Parallel arms share 20 cores, and the contention changes which
  wall each arm hits. Census arms may be run in parallel, because churn and adds-per-event are
  throughput-independent; gate arms may not.
* **Repeat a gate arm at least three times before quoting an outcome.** One configuration produced
  4.7x different event counts and both outcome kinds on two runs (Claim 90).

## 4.15 An arm that does less work always "passes" the memory gate

Three different arms reported `oom=0` in one session for three reasons, none of them memory
efficiency (Claim 97): CPU starvation from parallel runs, an outright STALL (`+0` events per interval
with hundreds of items queued), and the wall clock arriving before the heap wall.

Before quoting `oom=0`, check ALL of:

1. the run was **solo**;
2. the **progress delta was non-zero** at the end -- read `Progress: p/q (+delta)` and confirm delta
   is not 0, because a stalled run allocates nothing;
3. a **longer-budget probe** still holds -- if IFDS 500 s gives `oom=0` and IFDS 1200 s OOMs at 518 s,
   the arm never passed anything;
4. the **event count is comparable** to the arms being compared against; an arm that dies at 400k
   events has not beaten one that dies at 2.2M.

Note that `Progress: p/q` is `totalProcessed/totalEventsEnqueued`, and `q` is a live QUEUE DEPTH, not
a countdown of remaining work. It swings by four orders of magnitude within one run. A small `q` is
not evidence of being near the end.

## 4.16 The forward vulnerability count is NOT the recall signal on its own

`Total vulnerabilities: N` counts what the forward scan DISCOVERED. The SARIF finding set counts what
the user is SHOWN. They differ whenever the log says `Filter out N vulnerabilities without traces`,
and a finding that is filtered out is a false negative from every point of view except the counter.

Claim 100 measured a lever (`contextCap`) that holds `Total vulnerabilities` at 4 while dropping the
SARIF set to 2, and proved the loss is caused by the lever rather than by truncation: the arms that
OOMed kept all four traces, and the arms that comfortably survived lost them, monotonically in the
cap.

Always quote all three together: forward status, `Total vulnerabilities`, and the SARIF finding SET
with the `Filter out` line. An arm is recall-preserving only if the SARIF SET is intact.

### 4.17 To attribute a LOST finding, add recall back -- never revert

A revert large enough to change the finding set is usually also large enough to change whether the
build converges, and a build that does not converge cannot be compared on findings: its SARIF set
is truncated by trace resolution, not by the analysis. Measured: reverting the 20 `ap/ifds/access/`
files from `a71573142` moved conductor from `rc=0, 65 s, 3 findings` to `rc=253, oom=2, 381 s, 2
findings`. Fewer findings, and none of them attributable.

So attribute a loss ADDITIVELY:

1. Start from the build that CONVERGES. Convergence is the fixed point of the experiment.
2. Switch exactly ONE suspect back to its old, more over-approximating behaviour, behind a flag.
3. Run both settings solo and compare the SARIF set (4.16).

An arm that restores the finding has named the mechanism. An arm that does not has eliminated it
for the cost of one build and two runs. Either way the result is attributable, because the only
thing that moved is the suspect.

Corollary: prefer a suspect whose OLD behaviour was the over-approximating one. "The commit made
this stricter" is a testable claim; "the commit rewrote this" is not.

### 4.18 When guesses run out, instrument the FLOW, not the population

Reading a large diff for something that looks like a discard produced two wrong attributions
(`0cece323c`, then the summary-compression threshold) and nine eliminated mechanisms. The counters
that solved the EXPLOSION -- per-method, at the `MethodAnalyzerEdges.add` choke point -- were never
pointed at the LOSS.

`FactWatch` (`-Dopentaint.factWatch=<substring>`) is that instrument: offered/accepted counts and
sampled facts for methods matching a watch list. Its report is emitted beside `Analysis done in`,
which a TIMED-OUT build still reaches, so a converging build and a non-converging one can be
compared on it directly -- the one comparison the finding set cannot support.

Ask "which call edge drops the fact", not "which file discards something".

### 4.19 `Running low on memory` names TWO phases -- never grep the prefix

The engine logs two guards with the same prefix and different meanings:

```
"Running low on memory, stopping analysis"          -- the FORWARD analysis
"Running low on memory, stopping trace resolution"  -- TRACE GENERATION, which runs AFTER the
                                                       forward analysis prints `Total vulnerabilities`
```

`arm2.sh` counted the prefix and failed `FORWARD` on either. Measured on the sound build: the
forward analysis finishes in 404 s of the 500 s budget at 67% of 8 GB and reports all 4
vulnerabilities, and every memory event occurs afterwards, in trace generation. Three of four sound
runs logged ZERO forward-phase guards.

Use `arm3.sh`, which reports `oomFwd` and `oomTrace` separately and judges `FORWARD` on `oomFwd`.

Two consequences:

* Any `oom` figure recorded before this correction is a MIXTURE and cannot be attributed to a phase.
  Re-measure before relying on it -- including "conductor does not converge, every sound arm OOMs".
* A finding can be found by the forward analysis and then lost in trace generation
  (`Filter out N vulnerabilities without traces`). `Total vulnerabilities` and the SARIF set answer
  different questions, and 4.16 -- judge recall on the SARIF set -- holds only when trace generation
  actually completed. When it did not, the SARIF set understates the analysis and `Total
  vulnerabilities` is the honest forward number.

### 4.20 Two `Analysis done in` lines are two PHASES, not two units

Phase 1 is a ~25 s pre-pass that carries no taint (`f2f = 0` at every method measured, in both
builds). Phase 2 is the taint analysis proper and is where builds differ: 379 s and 3,287 tainted
edges at `HttpTask#start` on the sound build, 3.6 s and 113 on the converging one. Timing or
counting "the analysis" without splitting the phases averages a 105x difference with a constant.

### 4.21 ThingsBoard is BISTABLE -- one run proves nothing there

Four solo runs of an identical configuration split into two modes:

| mode | TIFA initials emitted | findings | time | forward guard |
|---|---|---|---|---|
| high | ~292,000 | 15/15 | 394 s | trips once |
| low | ~21,000 | 14/15 (loses `unsafe-reflection`) | 724-759 s | none |

Three of four runs landed low, one high. So a single ThingsBoard run cannot distinguish a lever's
effect from which mode it happened to hit, and several rankings taken that way have been withdrawn
(`Claim 114`).

Rules:

* Report the MODE with every ThingsBoard result. `TIFA EMIT: emitted=N` separates them cleanly
  (~21k vs ~292k) and costs nothing.
* Repeat until 3 runs agree or both modes appear. Treat a lone 15/15 as "the high mode happened",
  not as evidence.
* A lever that appears to lose a finding in ONE run has probably just landed in the low mode. Confirm
  before attributing.

The suspected cause is the known interner data race, which makes exploration order -- and therefore
how many initials TIFA emits -- differ between runs.
