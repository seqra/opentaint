# Physical mark requests lost their caller block owner

The actual `BenchmarkTest01875#doPost` regression is reproduced and recovered by preserving the block scope of a physical call's returning mark request. The clean RED diagnostic reports no finding; the GREEN diagnostic reports the exact trust-boundary sink `%30.setAttribute(bar, "10340")`. Both finish at run-3. These are single-root diagnostics using saved OWASP bytecode and production prescan, rule selection, JIR lowering and bidi execution. They are not a new four-project measurement.

| Diagnostic | Runtime | Result |
| --- | --- | --- |
| RED, `actual-trust-jir-engine-upstream-clean-20261103.log` | `1e6c43963868dde6f652a4b9fa0284c95c818b2c` | COMPLETE, run-3, zero trust-boundary findings |
| GREEN, `actual-trust-jir-engine-scoped-green-20261103.log` | Same base plus the scope-preserving request patch | COMPLETE, run-3, one exact trust-boundary finding |

The [portable data artifact](bidirectional-loop-block-scoped-request-gap-20261103.json) embeds the complete relevant trace lines, their original line numbers, log hashes, the runtime patch, source pins, actual Java sample, and frozen external audit/engine sources and Gradle init script. The observer delegates to production services; it does not insert seeds, initials, demand, cached contributors or plans. The configuration is FULL, limits `1,1,2,3,4`, REPEAT_RUN1, default getter models and alias analysis at depth 1. Only `doPost` is an analysis root.

The first lost owner is in run-1's physical request return, after the helper requests DATA. Source generation and block input transport already work. RED creates cookie root and element DATA/NORMAL at instruction 1, and retains `var(27).ANY/DATA DEMAND` as an input of AL47. The helper receives an abstract argument from caller slot `var(27)` in `BlockScope(block=3, entry=47)`. Its conditional encoder source requires DATA and the independently generated encoder marker. It requests DATA on that argument, but the returning request is applied to ROOT instead of AL47. ROOT has only its ZERO initial, so it cannot activate AL47's waiting input.

The compact chain below uses DATA for the full trust-boundary DATA mark, `L` for loop block 2 and `AL47` for block 3 / entry port 47. The JSON retains the full marks and packets.

```text
RED R1  640–641  getCookies -> Result.$/DATA NORMAL + Result.[*]/DATA NORMAL
RED R1  753–804  L: var12 FLOW -> cookie var16 ANY FLOW -> decoded var22 ANY FLOW
RED R1      913  AL47: physical helper subscriber, var27 FLOW -> helper arg1 FLOW
RED R1 1035–1037 helper source15: DATA REQUEST on arg1
RED R1 1054–1055 ChangedRequests(helper,arg1,DATA) -> MarkRequestsIn(caller,var27,DATA)
RED R1     1203  AL47 already retains var27.ANY/DATA DEMAND
RED R1     1234  ROOT initials = {ZERO}; AL47 never gets a DATA initial
GREEN R1   1114  AL47 now supplies var27.STAR/DATA DEMAND -> helper arg1
GREEN R1   1149  source15 emits Result.$/DATA DEMAND
GREEN R3   1652  source15 emits Result.$/DATA NORMAL
GREEN R3   1668  AL47 setAttribute sink fires NORMAL
GREEN      1703  exact trust-boundary finding is reported
```

The RED event trace prints method, slot and mark, but not event scope. ROOT dispatch is established by the pinned RED implementation: `ClimbTarget` drops `CallerRef.scope`, batches by method, constructs a method-only `MarkRequestsIn`, and the handler invokes the root analyzer. The subscriber's required AL47 owner and its waiting DATA packet are directly observed. GREEN changes that transport and recovers the same real sink. This identifies the concrete routing defect; it does not attribute the earlier generic ZERO or permission hypotheses to this miss.

The selected [scope-preserving request contract](../../spec/scoped-request-climbs.md) requires the following dispatch and prefilter behavior:

| Operation | RED implementation | Fixed implementation |
| --- | --- | --- |
| Climb identity | `(method, slot)` | `(method, scope, slot)` |
| Batch destination | Method | Method and exact block scope |
| Sender prefilter | Reads ROOT request history for every destination | Reads ROOT history only for ROOT; nonroot requests use destination-local deduplication |
| Event and delivery | Method-only event, root insertion | Event carries scope; method actor dispatches to the existing named block state |

The correction preserves the existing FLOW matching, selected slot and full marks. Direct TAINT answers and static-origin requests keep their existing paths. It changes neither ZERO admission nor C2/C5, source permission, source rules or layer policy. Actual lowering also confirms ordinary Cookie.getValue and URLDecoder copies preserve scalar EXACT/NORMAL DATA; string-byte return cleaners lie on the ordinary returned branch, which the explicit encoder source bypasses.

The earlier trace that queried a closed runner during observer freeze is excluded; the clean RED run has no observer error. The first JVM test invocation was separately blocked by stale repository test APIs, so the successful diagnostics use an isolated external source set against main dependencies.

The measured four-project campaign at `1e6c4396` remains OWASP **4,111 versus baseline 4,112**. This report proves recovery of the single-root case only. Whole-project quality and performance after the correction require the subsequent campaign.
