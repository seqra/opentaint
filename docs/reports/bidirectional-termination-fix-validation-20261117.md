# Verification of the demand-termination examples

**Scope.** This report verifies the combined reference, including the
[deferred Target-retirement rules](../../spec/demand-target-retirement.md).
Stops that use those rules apply to that reference scope.

All **24 in-scope entries** in the [termination catalogue](bidirectional-demand-termination-counterexamples-20261115.md#status-map) have a natural stop in their checked reference scopes. The MAY-producing pass rule is excluded. Eleven examples were rechecked with their optional reply omissions withheld. In those cases, the existing R38 root Target rule is enough once all required marking-to-observer tracks have a NORMAL witness.

The production driver at `966a40c36` does not implement the complete reference protocol. The native suite passed **2,689 tests in 436 classes**, including diagnostic fixtures and isolated adapters. Lean checked **16 additional constructive claims**, for **7,554** cumulative claims.

## Results

| Catalogue entry | Natural stop | Verification |
| --- | --- | --- |
| Recursive wrappers | run-7 with one origin, run-9 with two | Complete origin accounting and frozen Target retirement. The mutual native control stops at run-5. |
| Descendant selected EXACT cleaner | run-1 | The selected MUST coarsening gives a NORMAL observation and empty handoff. |
| Nested ALL/BELOW cleaner | run-3 | Exact residuals. Selected BELOW retains the boundary point. RemoveAll/ALL also stops at run-3. |
| Protected caller input | run-9 | With all optional reply omission withheld, the complete bound NORMAL track is present at run-5. |
| Uniform-input control | run-11 | With all optional reply omission withheld, the complete track is present at run-7. |
| Protected relevant returns | run-9 | The witness keeps the literal H in all three bindings and is complete at run-5. |
| Protected unrelated NORMAL return | run-11 | The complete track is present at run-7. The unrelated return stays in the body closure. |
| Same-mark disjoint return | run-11 | The complete observer track is present at run-7. The other return is accounted for in the body and caller read. |
| Unadmitted NORMAL V return | run-9 | The U observer track is complete at run-5. The V output has no route through its actual field guard. |
| Exact input without overwrite | run-9 | The complete bound track is present at run-5. The earlier delayed-readiness control reaches run-7 with certified reply service. |
| Deeper real exclusion | run-5 | The exclusion stays at the actual head. The stop also holds with the optional uniform fold withheld. |
| Real exclusion and unrelated output child | run-5 | The actual E is retained and the unrelated field stays disjoint. The stop also holds with the optional fold withheld. |
| Alternating conditional generators | run-7 | The retained run-3 computation supplies all eight ordered NORMAL tracks. The first eligible Target omission is at the run-5 handoff. |
| Root MAY renewal | run-5 | Complete method reference, with the expected observation. |
| BB and enclosing-method renewal | run-5 | Complete block and enclosing-method reference, with the expected observation. |
| Global-cut growth | run-3 | The ordinary two-call reference empties its demand. |
| Uniform root cleaner | run-1 | NORMAL observation and empty handoff. |
| Protected global-cut growth | run-3 | Protected fixed-point packet has no outgoing demand. |
| Nested saved replay | run-9 | Child service accounts for saved-first application with empty current demand. |
| Saved replay with real exclusions | run-9 | Same child service with real E kept at its owning head. |
| EXACT-origin nested write | run-3 | Strict-descendant expansion gives no invented observation. The same-head overwrite guard remains. |
| Direct concrete MUST replay | run-7 | Both independent bindings have NORMAL witnesses by run-5. Retain the provisional reply and retire only the root Target. |
| Uniform saved reply | run-7 | Both independent uniform bindings have NORMAL witnesses by run-5. The provisional reply is retained. |
| Different-path uniform replies | run-7 | Three distinct marking-site, call-binding and observer tracks have NORMAL witnesses by run-5. The field input cannot satisfy the unrelated g guard. |

The stop in each row requires an empty forward frontier. No proof uses the run-11 runtime cutoff. The direct-replay regression also evaluates all 18 ordinary variants from the cold start and checks closure before recognizing an empty frontier. Its latest natural stop is **run-17**.

## How the strengthened guards are exercised

- **Saved MUST and alternating generators.** Keep the possible replies. Validate each marking route using the actual call binding. The root Target has only the identified observation and backward source-permission consumers in these fixtures. Once these obligations are met, R38 can retire the Target with the frozen receipt. It leaves DATA rows and NORMAL observations in place.
- **Bound replies.** Enumerate the three ordinary call steps using the exact source, whole rule body and actual caller field read. Use each fixture's real observer mark. For each possible observing route, require a committed NORMAL witness at every hop with the same mark and H. Check the fresh result against its own prepared C2/C5 pair, or replay an available saved record. One further round equals the observed fixed point at every active run. After Target omission, the remaining DATA frontier drains. The sealed inactive state cannot recreate a seed.
- **Disjoint recursive field routes.** An empty product or closed nested state-pair certificate supplies NoRoute only for its own observer. A separate unresolved control use keeps the Target. Both disjoint fixtures reach natural run-5. Positive shared-word controls retain the observation at run-5 or run-7.

The earlier protected and uniform diagnostic used `history false`. This switches off uniform value folding and still allows bound-reply omission. The corrected control forwards every applicable reply. With this control and no R38 certificate, each bound case still has a Target at the run where the certified reference stops.

## Additional diagnostics

- R17 keeps the only late marking route when the other source already has the same NORMAL report. The native adapter preserves the second track at run-5. The loop-exit guide with a NORMAL backward ZERO premise preserves the observation at run-3.
- The two-source actual loop and nested loop controls reach run-13 and run-17. The run-2 STAR relay and disjoint-cleaner getter repairs reach run-3. The direct prefix-return control reaches run-5 with its expected NORMAL observation.
- The long shared-word native control finishes at run-5 without the expected observation. The reference reaches it at run-13. The root guard performs zero rewrites on that native case. The nested writer scalar pilot repeats at diagnostic run-9 while the native version naturally stops at run-5. These are alignment diagnostics outside the 24 catalogue entries.

The verification is scoped to the explicit reference bodies, paired publications and root consumers. Native activation still requires correspondence for the actual scheduler, source permissions and physical ports.

## Reproduction

See the [Lean verification package](../../spec/lean/proposals/termination-catalogue-verification-20261117/README.md) for the constructive checks and cold replays. The external archive is `termination-catalogue-verification-20261117`.

```sh
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --offline --rerun --tests 'org.opentaint.dataflow.bidi.*'
```
