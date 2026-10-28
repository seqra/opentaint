# Restricted demand: selected repair checks

Date: 28 October 2026. Status: **local checks complete; project campaign pending**.
Base: `86eb2f04377a9cef7648b1c1152f9c55da182787`. The runtime updates and
this report belong to the same implementation change. The contract is
[restricted-demand-static-closure.md](../../spec/restricted-demand-static-closure.md).
This is not a landed-commit performance report.

No project scan has started for this change. The full local cleaner checks
reach, complete and accept **run-9**. The focused transition checks reach,
complete and accept **run-3**. The five tests that lost the
final finding now pass. Real JVM checks also keep the finding through
run-3, with FULL and GROUP marks and two returning wrappers.

## Selected changes and evidence

| Check | Result | What it establishes |
|---|---|---|
| Abstract STAR demand normalization | 95 focused tests pass | Entry/exit Empty E, shared FLOW start, scalar/packed agreement, unchanged concrete/actual/native E and protection |
| New exclusion tests before/after fix | Nine tests: seven fail before, none fail after | The new behavior is checked rather than inherited from the old oracle |
| Abstract demand local model | 19 constructive audits pass | Demand widening/idempotence, C2 against normalized demand, C5 raw-pair/layer preservation and actual-E matching |
| Static STAR input correction | 44 focused tests pass | Named-field STAR/E relay, no-demand/no-start, actual mark gate, bounded paths and retained negative grammar checks |
| Static input local model | 15 constructive audits pass | Grammar extension, bounded STAR identity/limit relay under explicit adapters |
| Immediate write supply and relay removal | 26 focused tests pass | Actual-input/request paths, FULL/GROUP, copy and T-to-U, exit kill, retained FLOW writer, aliases and existing computed summary supply |
| Local write supply model | 14 constructive audits pass | Admission/write witnesses, mark output, FLOW retention, exit independence, idempotent pool union, no new NORMAL record |
| Lost exit-key model | 25 constructive audits pass | Exact pending/final partition, nonmonotone survivors, complete key preservation, seed-only binding and closure transport under explicit adapter contracts |
| Binding scope witness | Six constructive audits pass | Counterexample to exact AP tail-key reassociation; exact closure theorem scoped after bound seeds freeze |
| Killed-write store and exit capture | 12 tests pass | Final-only survivor pruning; raw mark mapping; normal/exceptional split; intermediate writes and late resumes; mutable candidate storage release |
| Exit/transition and frozen closure controls | 27 tests pass | The original five lost-finding cases now pass; genuine ZERO writers and returning wrappers keep run-2 source guidance and the run-3 finding |
| Real JVM killed-write checks | Two tests, six FULL/GROUP cases, pass | Production exit-rule static drop, a source inside the getter, zero/two returning wrappers, and an unmarked-write negative control |
| Joined writer binding | Eight tests pass | Exact caller context, real ZERO controls, recursive admission, raw mark exclusions, no repeated request effect, cancellation and an independent deadline watcher |
| Measurement helpers | 42 tests pass | Separate engine/completion timing, candidate counters and CPU sample windows; failed completion is not an accepted complete run |

The focused suites overlap. Their counts must not be added into a unique
test total. Their XML, commands, logs and source hashes are saved under
`/drive-testcomp/opentaint-go-rules/restricted-demand-20261028`:

- `abstract-demand-focused-checks.json`
- `static-star-domain-focused-checks.json`
- `local-static-supply-focused-checks.json`
- `killed-write-current-red-checks.json`
- `killed-store-hooks-checks.json`
- `joined-transition-first-common-checks.json`
- `joined-transition-jvm-checks.json`
- `joined-writer-binding-focused-checks.json`
- `measurement-helper-tests.log`

The first combined test command passed the 27 common checks. Its JVM
task did not run: an unrelated Go server rebuild failed because the local
`protoc` does not accept the schema. The JVM-only command then passed with
that rebuild excluded. It uses the existing Go artifact and changes no
JVM analysis setting.

Proof receipts are beside their models under
`spec/lean/proposals/restricted-demand`. Only `propext` and `Quot.sound`
occur in the combined local audits; there is no classical choice or
unproved placeholder. These are local contracts, not a whole-JVM proof.

## Remaining acceptance

The thin candidate store, final pruning and caller binding are implemented.
Binding runs after workers stop and before caller inputs release. It uses
the existing caller index and creates guidance only. It does not run
rules, emit summaries, supply the static pool or start work. A separate
deadline watcher keeps the same time limit active inside AP operations.
Candidate pruning, writer binding and closure freeze have separate times
and aggregate counters. The initial publication/query replacement remains
as specified. STAR inputs do not add STAR rule literals.

The complete local results are below. Commit the selected iteration, then run the four
configured project measurements, reusing baseline `f945f92c5ae554ff4f5fc7696ee5a269210478bb`.
Record engine and transition times, latest reached/completed/accepted run,
finding differences, CPU/heap evidence and candidate/binding/closure work.
Rank the next optimization proposal from those measurements. None of
those project outcomes is claimed by this report.

## Complete local suites

| Suite | Tests | Failures | Skipped |
|---|---:|---:|---:|
| Common | 1,999 | 0 | 0 |
| JVM module | 440 | 0 | 0 |
| Go module | 1,323 | 0 | 0 |
| Application | 1,041 | 8 | 13 |

The application failures are eight exact-precision checks for cleaners.
All expected finding IDs remain. They contain 26 extra IDs across the
eight test invocations: 11 in three control-flow cases and 15 in five
mark-count cases. Each exact missing/extra set equals the prior 27 October
local result. This is an existing precision limit, not an all-green result.
The [complete comparison](data/bidirectional-restricted-demand-cleaner-precision-20261028.json)
contains each test, expected/actual counts, exact extra IDs and run-9
frontier evidence. The cleaner tests and their expectations remain unchanged.

The smallest case has empty field exclusions. Thus, ignoring abstract
demand field exclusions cannot explain that case. An AP operation can
retain a DEMAND residual after a partial exact cleaner. The restored shared
FLOW start and paired restriction can expose that residual. These facts
show a possible mechanism, not a captured end-to-end cause for each extra
finding. No cleaner transfer change is included in this iteration.

The first common run found six old-contract assertions. Tests now check
the selected abstract-exclusion and immediate-write-supply behavior; the
synthetic normal ND handoff case runs in run-3. Concrete/native exclusion,
complete guard and contributing-origin checks remain. A complete common
rerun then passed. No expected finding was removed from these tests.

Full XML and source bindings are in `full-common-final-checks.json`,
`full-local-first-checks.json` and `implementation-proof-bindings.json`
under the experiment directory above. All five selected proof sources
still match their pre-implementation audit hashes: 79 local audits.

The fresh input comparison passes all 25 content datasets and all four
project models against the saved baseline inputs. It checks classes,
dependencies, source roots, toolchains, rules and conductor extensions.
It does not run the baseline analyzer. The fixed project campaign remains
the next acceptance step.
