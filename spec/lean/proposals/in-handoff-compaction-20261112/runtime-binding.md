# Runtime binding for work reduction

This note binds the implementation to the selected
[proposal](../../../../docs/design/bidirectional-work-reduction-implementation-20261112.md).
The four Lean sources retain their original scope. Their 79 local claims do
not prove all Kotlin code. Native differential tests check the runtime binding.
Residual R3 MAY removal remains disabled. No iteration cap proves a removal.

| Model | Runtime binding | Native check |
| --- | --- | --- |
| `HandoffCompaction.lean` | `HandoffServiceKeys` keeps complete owner, ports, marks, exclusions and literal protection. `projectSummaryGuidance` visits every premise member and conclusion leaf. `HandoffCompactor` removes guidance only with retained C2 and C5 providers. | `HandoffCompactorTest` compares complete initial families and native C5 results from actual stores before and after selection. It also checks ND completeness, ports, controls, arrival order and the inactive MAY case. |
| `ImplementationAlgorithms.lean` | Handoff certificates name final active providers. The reverse dependency map selects the certificates that need repair before a provider can be removed. Caller fallback keeps one stable handle and removes only the migrated source. | Handoff final-provider and rebinding tests; caller source migration, snapshot and posting-order tests. |
| `WorkReduction.lean` | The single trie walker stops the whole scan. Strict descendant C2 candidates are omitted only for STAR/EXACT inputs. A loop probe compares complete scope/family/pattern/layer descriptors; a negative witness rejects one trial. A completed trial still needs full observation equality. | `FrozenDemandTrieTest`, `LoopAdmissionProbeTest` and existing demand/loop differential controls check order, companions, exclusions, cancellation, preflight, cache reuse and missing-only differences. |
| `CallerMarkRelations.lean` | Each family keeps literal diagonal memberships and target-to-source sets at each private coordinate. Decode restores a complete native packet before all consumers. Native `mergeAddDelta` remains the delta operation. | `CallerInputValuesTest` checks every offer against `AddedFactAccumulator`, including all 512 small changing-mark relations. `PackedCallerDeliveryTest` checks complete consumers, finite request visits and snapshot/posting order. |

The disabled diagnostic path uses a separate optional capability. This keeps
`UnresolvedCallObserver` a Java/Kotlin SAM. Generic observers remain enabled.
The JVM observer is enabled only when its immutable tracker is present.
`RunMethodCallServices` allocates its archive on the first eligible enabled
TAINT observation. Tests retain the old enabled counts, preserve transfer and
check that the disabled path creates no archive. A Java lambda compilation
control checks the SAM contract.

Two packing controls close implementation boundary cases:

```text
Exact-only internal packet with noncanonical any-tail header:
    keep scalar authority; do not canonicalize it through packed decode.
    A later unsupported offer migrates only its existing source.

Output field coordinate:
    copy it into the family-owned coordinate key.
    Do not add it to the manager's strong premise-path interner.
    Release the coordinate with its family/directory.
```

The header cases first failed in native tests. The scalar fallback correction
then passed. The ownership test checks that output-only coordinates do not
grow the strong premise-path interner. Neither correction changes AP transfer,
C2/C5 rules, layers, marks, protection, aliases or report identity.

Packing uses the existing shared `PathTrie<Int>` as its thin candidate index.
This directly preserves first successful path/handle posting order, including
late positions and migration. It removes the retained per-source packet
value, not the candidate-order contract. No scalar packet mirror is retained.
Native reconstruction and target-bucket scans remain costs to measure.

The optional packing census is recorded once when a directory is released.
Its totals are cumulative released-directory counts. They are neither a
simultaneous heap census nor globally deduplicated geometry.

Detailed logs, source hashes, failed attempts and copied native XML files are
kept outside the repository in
`/drive-testcomp/opentaint-go-rules/work-reduction-20261112/native/`.
Project results and full-suite results must be read from the fresh validation
report. A focused passing test is not a project-performance result.
