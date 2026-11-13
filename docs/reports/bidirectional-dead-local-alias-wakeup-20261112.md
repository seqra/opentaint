# A late FLOW admission can wake an old concrete local

12 November 2026. Runtime source pin: `14d7b63369d94f49d4c551be8405ed7719f267cc`.
Current campaign target `1025a197…` remains OPEN. This is a native core fixture,
not its actual method and not a valid-sink-loss or necessity proof. No project
scan was made. The compatible OWASP project frontier remains
reached/completed/accepted run-11.

## Result and scope

A late FLOW initial can register a new reverse-loop target. Registration can
then start an old concrete local at that target, although the local's own
boundary route was removed by liveness. A reversed ALIASES stage can transfer
that local to a source-rule position. The native source handler then records
a source hit and emits DemandTarget.

**FLOW does not create the concrete mark.** The concrete mark comes from an
old admitted initial. Target registration replays that initial.

The fixture supplies the old local at a core boundary. It manually specifies
instruction metadata and a call plan with an alias output. It does not prove
that real JIR lowering and alias analysis can produce this state. In particular,
it does not establish positive input alias closure at this block interface.
It is a counterexample to unconditional callback independence at the core
operator level. It does not prove a valid finding is lost.

## Native fixture and facts

The CFG is the successive-loop case from the fan-out check:

```text
0 -> 1; 1 -> {2,3,4}; 2 -> 1;
3 -> 5; 4 -> 5; 5 -> {6,7}; 6 -> 5; 7 -> 8.
8 is normal exit; 9 is the separate exceptional exit.
```

`X = LocalVar(0)`, `Y = LocalVar(1)`, `Q = arg(1)` and `A = arg(0)`.
Instruction 3 mentions X. Instruction 4 has a call operand Y. No reverse
path from 4 mentions X in the supplied instruction metadata. Thus the native
backward liveness mask retains X at 3 and drops X at 4.

The call at instruction 4 has these forward stages:

```text
BIND_IN:  BEFORE -> BOUND       Z -> Z
SOURCES:  BOUND -> REWRITTEN    Z -> A.$/T; Z -> Z
ALIASES:  REWRITTEN -> AFTER    A.*/FLOW -> X.*/FLOW
                                  [ordinary MemoryEffect guard]
```

The fixture passes this plan to the real `RunMethodCallServices`. The ordinary
`CallPlan.reversed` supplies the backward stages. It adds the alias base X to
the reversed plan's touched bases. Thus syntactic non-mention of X does not
by itself prohibit this backward alias operation.

The supplied demand admits X/T on its retained routes and allows its Target
result. The two variants differ only in whether they also admit Q/FLOW.
Saved NORMAL records, instruction metadata, X demand and source stages are
unchanged.

```text
Run-12: submit X.$/T,NORMAL
  first-loop shared scope = (block 2, entry port 11)
  X route 3: retained; C2 admits X.$/T,NORMAL
  X route 4: liveness drops the route
  registered starts = {3}
  source hits = 0
```

Then submit Q/FLOW:

```text
With Q/FLOW demand:
  Q is nonlocal; route preparation keeps both 3 and 4
  C2 admits Q.$/FLOW,NORMAL
  target 4 becomes registered
  offerChild queues every old admitted initial at target 4
  old X.$/T,NORMAL starts at 4 without the route liveness check
  reversed ALIASES: X.$/T -> A.$/T,NORMAL
  reversed SOURCES: A.$/T -> Z,NORMAL
  acceptedSource records the actual forward Z -> A.$/T source occurrence
  original X/T -> DemandTarget is emitted
  registered starts = {3,4}; source hits = 1

Without Q/FLOW demand:
  saved NORMAL Q summaries still replay
  current C2 emits no Q initial; admitTarget is not called
  registered starts = {3}; source hits = 0; no Target
```

## Saved NORMAL providers are actual inferred results

Each variant first runs a pure-Q training fixture at run-10. It records no
source hit. Its actual NORMAL method and scoped summaries are persisted through
`PersistentRecordStore.persist` and `persistScoped` before run-12.

All 13 provider relations are `Q.*/FLOW -> Q.*/FLOW,NORMAL`, with empty field
and mark exclusions. The complete scope/port coordinates are:

| Owner block | Entry | Exit |
| --- | ---: | ---: |
| Method root | ROOT | ROOT |
| 1 | 0 | -1 |
| 2 | 11 | 0 |
| 2 | 11 | 4 |
| 2 | 4 | 0 |
| 2 | 4 | 4 |
| 3 | -2 | 11 |
| 4 | 11 | 11 |
| 5 | 12 | 11 |
| 5 | 12 | 9 |
| 5 | 9 | 11 |
| 5 | 9 | 9 |
| 6 | -2 | 12 |

The native test checks exact complete coordinates, including owner, premise,
conclusion, tail, exclusions and layer. With Q admission, its 13 current FLOW
AP outputs are all in this trained NORMAL set. Without Q admission, it has
zero current FLOW AP outputs. Saved replay remains available in both variants.
No Target or source-hit coverage is inferred from this AP subset check.

## Proof boundary

The finite initial-by-target join model remains unchanged and valid. It shows
that target registration starts every old initial at a new target. It does not
show that each old local independently reached that target: liveness can remove
its own route, as this fixture demonstrates.

The selected positive input-alias-closure contract may give an independent Y/T
route for a genuine X/Y alias. This fixture does not establish that route at
the block interface. Without a native adapter proof or a faithful JIR example,
we cannot infer either whole FLOW-family retirement or campaign necessity.
The current target remains OPEN. No source/CFG/JVM eligibility guard is added.

## Reproduction and evidence

External case:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/
  redundant-demand-rows-20261112/cases/dead-local-alias-wakeup-v1/
```

`DeadLocalAliasWakeup.java` uses real C2, block routing, liveness, call-plan
reversal, alias/source application, source-hit capture and Target publication.
`execute.txt` has the two full traces, all 26 printed training provider rows,
the exact-subset checks and the terminal PASS marker. The source-built pinned
runtime and preserved pinned fixtures are unchanged. `reproduce.py` writes
new verification output to a separate directory. No production file was edited.
