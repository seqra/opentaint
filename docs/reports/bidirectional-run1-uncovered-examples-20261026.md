# Run-1: examples retained for reasons other than the flag — 2026-10-26

These are real Conductor raw-summary examples from a separate completed **run-1** diagnostic. Latest reached, completed, and accepted forward report: **run-1**. FULL marks and field limit 1 are used. Production analyzer code is unchanged.

Every concrete example is still retained when its non-subsumable annotation is removed on a temporary copy. This directly tests the [“Not covered for other reasons” category](bidirectional-run1-protection-coverage-20261026.md). These are examples, not a population estimate of each reason.

For each case, the first FLOW list contains **all rows under the corresponding abstract initial in the same raw method-summary store**. FLOW rows under other initials are listed separately. They require another input dependency and cannot substitute for the shown initial. No method FLOW list is truncated. Sampled methods have at most 16 FLOW leaf annotations.

Notation: `F` is the abstract FLOW mark slot, not a concrete mark. `*`, `[any]`, and `$` are the actual STAR, ANY, and EXACT field tails. Layers are printed explicitly. All shown field-exclusion sets are empty; mark exclusions are printed on each FLOW output. `Element` is the synthetic `java.lang.Iterable.Element` field, not a root leaf.

Concrete mark aliases:

- `Tsql` = `java/security/sqli.yaml:sql-injection#source#1;0;$UNTRUSTED;2`
- `Tssrf` = `java/security/ssrf.yaml:ssrf#source#1;0;$UNTRUSTED;2`
- `Ussrf` = `java/security/ssrf.yaml:ssrf;2;$<ARTIFICIAL>_20;2`
- `Tgrpc` = `java/lib/spring/conductor-grpc-request-sources.yaml:conductor-grpc-request-sources;0;_<T>_;`

## 1. Different field tails

Method: `org.conductoross.conductor.core.storage.FileStorageServiceImpl#confirmUpload(java.lang.String) [{}]`.

Concrete member (flags ignored):

```text
arg0.*/Tsql -> ret.fileHandleId.[any]/Tsql [DEMAND]
```

All matching-initial FLOW rows (2):

```text
arg0.*/F -> arg0.*/F [NORMAL]
arg0.*/F -> ret.fileHandleId.*/F [DEMAND]
```

There are no FLOW rows under other initials in this method.

The only return-field FLOW row has a STAR tail. The concrete row has ANY. The current replacement cell requires FLOW ANY and TAINT ANY. Moving FLOW to DEMAND does not change its STAR tail.

## 2. FLOW reaches collection elements, not the result root

Method: `com.netflix.conductor.core.dal.ExecutionDAOFacade#createTasks(java.util.List) [{}]`.

Concrete member (flags ignored):

```text
arg0.*/Tsql -> ret.[any]/Tsql [DEMAND]
```

All matching-initial FLOW rows (3):

```text
arg0.*/F -> arg0.*/F [NORMAL]
arg0.*/F -> ret.*/F [NORMAL]
arg0.*/F -> ret.Element.[any]/F [DEMAND]
```

Other FLOW initials in this method (1 row; not replacements for this initial):

```text
this.*/F -> this.*/F [NORMAL]
```

The return-root FLOW row has a STAR tail. The ANY FLOW row reaches ret.Element. Its field path is not a prefix of the concrete output path at ret. A branch below the root is not a FLOW leaf at the root.

## 3. The matching ANY FLOW excludes the mark

Method: `org.conductoross.conductor.ai.document.DocumentAccessPolicy#normalizeLocation(java.lang.String) [{}]`.

Concrete member (flags ignored):

```text
arg0.*/Tssrf -> ret.[any]/Tssrf [DEMAND]
```

All matching-initial FLOW rows (3):

```text
arg0.*/F -> ret.*/F [NORMAL]
arg0.*/F -> ret.[any]/F - {Tssrf, Ussrf} [DEMAND]
arg0.*/F -> arg0.*/F [NORMAL]
```

Other FLOW initials in this method (1 row; not replacements for this initial):

```text
this.*/F -> this.*/F [NORMAL]
```

The ANY return FLOW row has the right geometry, but explicitly excludes Tssrf. The NORMAL STAR row permits Tssrf but has a different tail. No single FLOW row meets both tests; properties from those two rows cannot be combined.

The same method also retains this cross-mark member:

```text
arg0.*/Tssrf -> ret.$/Ussrf [DEMAND]
```

It changes Tssrf to Ussrf. FLOW preserves the incoming mark and cannot provide that mark-generation relation. Its EXACT output also fails the current ANY-only cell. The FLOW list above is complete for this example too.

## 4. Same geometry, different summary effect class

Method: `com.netflix.conductor.core.dal.ExecutionDAOFacade#searchTaskSummary(java.lang.String, java.lang.String, int, int, java.util.List) [{}]`.

Concrete member (flags ignored):

```text
arg4.*/Tsql -> arg4.[any]/Tsql [DEMAND]
```

All matching-initial FLOW rows (3):

```text
arg4.*/F -> arg4.*/F [NORMAL]
arg4.*/F -> arg4.[any]/F [DEMAND]
arg4.*/F -> ret.results.[any]/F [DEMAND]
```

Other FLOW initials in this method (4 rows; not replacements for this initial):

```text
arg0.*/F -> arg0.*/F [NORMAL]
S["__spring_registry__"]["com.netflix.conductor.dao.IndexDAO"].*/F -> ret.results.[any]/F [DEMAND]
arg1.*/F -> ret.results.[any]/F [DEMAND]
arg1.*/F -> arg1.*/F [NORMAL]
```

The concrete arg4-to-arg4 relation is classified as having no memory effect: its bases, field chains, and concrete marks agree. The FLOW ANY relation is classified as an effect. The summary normalizer keeps this identity/effect distinction. The NORMAL STAR identity has the same identity classification but a different tail.

## 5. An exact output is outside the current ANY cell

Method: `org.conductoross.conductor.ai.tasks.worker.DocumentGenWorkers#storeDocument(java.lang.String, byte[]) [{}]`.

Concrete member (flags ignored):

```text
arg0.*/Tgrpc -> ret.$/Tgrpc [DEMAND]
```

All matching-initial FLOW rows (2):

```text
arg0.*/F -> arg0.*/F [NORMAL]
arg0.*/F -> ret.[any]/F [DEMAND]
```

There are no FLOW rows under other initials in this method.

The output is EXACT ($), while the matching FLOW output is ANY. The current normalizer removes diagonal ANY memberships; it retains exact leaves. This is an implementation cell boundary, not a claim that no broader subsumption law can be proved.

## 6. A generated mark has a ZERO initial

Method: `com.netflix.conductor.rest.controllers.TaskResource#getPollData(java.lang.String) [{}]`.

Concrete member (flags ignored):

```text
Z.$/<zero> -> ret.[any]/Tssrf [DEMAND]
```

All matching-initial FLOW rows (0):

```text
(none)
```

There are no FLOW rows under other initials in this method.

The concrete mark is generated with no input dependency. This method has no FLOW summary rows. A mark-preserving FLOW relation cannot express this ZERO-origin mark generation.

## Interpretation and checks

Tail, EXACT, and identity/effect examples show limits of the current replacement cell. They do not prove that every broader replacement would be unsound. Mark exclusions and cross-mark generation are separate constraints. A geometric match alone is insufficient.

The diagnostic reuses `FlowBackedSummaries.normalize`. It first clears protection on a copy, then samples the retained residual and checks the corresponding one-member value again. Four targeted tests pass: tail mismatch with complete FLOW preservation; exclusion of flag-only cases; cross-mark output; and mark-exclusion preservation. A test also checks that the store census does not change.

The base runtime is `30b50b20029394eee9c34acb5afce934b08591b9`; the core tree is `e3ede1a36d3b04d79a23cc93285f385ecd968dbf`, identical to the current production core. A new detached checkout adds only diagnostic reads and stops after the ordinary run-1 report/handoff. Inputs, Java 17, aliases, statics, FULL mode, 16 GiB heap, and timeouts match the prior Conductor campaign.

The [machine-readable evidence](bidirectional-run1-uncovered-examples-20261026.json) preserves all sampled candidates, complete per-method FLOW lists, canonical field/mark IDs, exact mark names, individual gate checks, manifests, source binding, and test results. Raw evidence is under `/drive-testcomp/opentaint-go-rules/run1-coverage-examples-20261026`.

Reason labels in the bounded sample use a fixed classification order. A concrete edge can fail several checks; those labels are not counts of independent causes. The source JSON retains every FLOW row so that these overlapping failures can be checked.
