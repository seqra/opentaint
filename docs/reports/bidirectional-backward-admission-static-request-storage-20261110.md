# Backward admission and shared static request storage

10 November 2026. Runtime: `14d7b63369d94f49d4c551be8405ed7719f267cc`.
This is a follow-up to the
[OWASP and TenantId investigation](bidirectional-owasp-demand-tenant-writes-20261110.md).
Production code is unchanged. The storage change below is a proposal, not an
implemented optimization.

OWASP reached and completed **run-11** and accepted forward **run-11**.
Thingsboard evidence is from **run-1 OOM**, with no completed or accepted run.

## 1. OWASP: the fact that answers the repeated demand

The earlier complete capture already contains the quoted forward relation in
**run-7**, before run-9. Its handoff reverses the relation:

```text
forward summary:
  param.bytes.[].* / FLOW -> ret.bytes.[any] / FLOW, DEMAND

next backward demand:
  entry = ret.bytes.[any] / FLOW
  exit  = param.bytes.[].* / FLOW
```

Here `bytes` means the model field `String#<string-bytes>`. `[]` is the
array-element accessor. The distinct `String#bytes` field has parallel rows;
the evidence keeps their native accessor IDs separate.

### Observed backward input and emitted initial

The new observer records the actual argument to the public
`DemandStore.initials` operation and its complete returned admission family.
Both **run-8** and **run-10** contain this cell:

```text
demand entry:   ret.bytes.[any] / FLOW
submitted:     ret.[any] / T, DEMAND
emitted:       ret.bytes.* / FLOW, NORMAL
initial edge:  ret.bytes.* / FLOW -> ret.bytes.* / FLOW, NORMAL
```

For example, one exact submitted T is:

```text
java/security/sqli.yaml:sql-injection#source#0;0;$UNTRUSTED;1
```

The second SQL source mark, `#source#1;0;$UNTRUSTED;2`, also takes this cell.
The actual packet has one root MAY leaf, empty field exclusions and no
protection. These are concrete submitted marks, not a submitted FLOW fact.
The helper's current demand asks for FLOW, so its emitted initial has FLOW.

This is the existing C2 rule where the demand path is below the actual path:

```text
actual prefix: ret
demand path:   ret.bytes
actual tail:  [any], so it can contain bytes
demand tail:  [any]
result:       demand path + STAR
```

The containing MAY fact can supply the demanded field. A root STAR input
would not pass this cell. There is no need for a submitted longer concrete
field chain. This is why the same shallow demand can be answered again even
when the global field limit increases.

The NORMAL layer is also the current C2 rule: abstract FLOW admissions use
their intrinsic layer. Concrete admissions inherit their input's uncertainty;
this FLOW admission is not concrete. A NORMAL local FLOW identity does not
confirm the caller's DEMAND marked input or its sink witness.

The complete lookup returns several initials for this packet, including
`ret.* / FLOW` and the parallel byte-field initial. The capture records all
of them; it does not attribute the entire family to this one demand row.
The specific `ret.bytes.*` cell above follows directly from the paired demand
and `RestrictedInitialPolicy.emit`.

### Why the obligation returns

The forward row is not removed merely because the next backward run admits
an initial for it. The demand store is an immutable input for one run. It
does not record that this paired obligation has been permanently answered.
Backward analysis emits another handoff, then the next forward run applies
C5 to its candidates again.

The preceding investigation proves the immediate forward cut:

```text
raw NORMAL: param.bytes.[].* -> ret.bytes.[].* / FLOW
matched row exit: ret.* / FLOW
effective output budget: FL(ret) + 1 = 1
result: param.bytes.[].* -> ret.bytes.[any] / FLOW, DEMAND
```

Another matching row permits a deeper NORMAL output. The current union of
per-row C5 results retains the shallow DEMAND output too. Thus this is a
repeated coarse obligation, not evidence of a path that still needs eight
or ten fields. This observation does not authorize dropping arbitrary paired
demand or stopping on equal counts.

### Diagnostic validation

The diagnostic retained FULL mode, aliases and statics, the `1,1,2,...` field
schedule, 8g and the 1000 s timeout. It completed run-11 with `RUN_LIMIT`,
2,633 confirmed findings and zero provisional findings. All 2,633 exact
rule/location identities match the preceding diagnostic: no missing or new
locations. The observer recorded 810 records with zero errors, including 56
actual C2 offers and 80 returned initials for the selected helper in backward
runs 4, 6, 8 and 10. Other records capture raw summaries and C5 in runs 8–10.

This run's frontier counts differ from the earlier captures. They are not
substituted into the performance report. These diagnostic times do not
measure the proposed storage change.

The [data record](data/bidirectional-owasp-backward-admission-20261110.json)
contains the exact admissions, the earlier run-7 demand, full mark names,
observer source, launch configuration and completion receipts. The
[complete native trace](data/bidirectional-owasp-backward-admission-20261110.jsonl.gz)
also includes all returned initials and the raw/C5 records.

## 2. Thingsboard: share the pending image across marks

The latest reached Thingsboard iteration is **run-1, OOM**. No iteration was
completed or accepted. This section uses the existing heap, not a new scan.

The two hot static fields have:

| Origin | Pending mark memberships | Pending points | Registered global FLOW writers |
| --- | ---: | ---: | ---: |
| `TenantId.tenants` | 1,396,027 | 55,770 | 251 |
| `TenantId.SYS_TENANT_ID` | 1,217,455 | 42,327 | 0 |
| All fields | 2,827,665 | 102,081 | 1,023 |

The two fields account for **92.425%** of the pending memberships. This is a
reader/continuation multiplied by marks pattern. It is not millions of writes.

### Current ownership and work

`Run1StaticService` already has one field state with disjoint `req`, `reach`
and `processed` sets. It sends a new request to existing writers only when
the mark becomes requested for that field. Each writer also remembers its
admitted marks. Repeating the same request at another reader does not repeat
that global writer request.

The large repeated population is in the owner-local continuation store:

```text
Run1PointResume:
  point key = instruction/stage + initial + output header + call state
  pending[fullMark] = mutable wrapper around the accumulated FLOW image

LocalStaticInputRequests:
  boundary key = local link + original + output header
  pending[fullMark] = accumulated FLOW image
```

On each new image, the current code unions it separately for every offered
mark. Most images do not need that separate representation:

- 90,206 points have one identical immutable root across their pending marks.
- Those points contain 2,640,824 memberships, **93.392%** of all memberships.
- Across all points there are 264,165 distinct point/root pairs, using pointer
  identity. Some distinct roots also have equal geometry.

The roots are already shared. A new proposal must reduce per-mark entries,
wrappers and repeated image unions, rather than claim to remove a separate
tree per mark.

### Proposed owner-local representation

Keep the existing point key and ticket. Replace its per-mark map with buckets
whose mark sets are disjoint:

```text
Point {
    key, ticket
    buckets: [(image: immutable FlowNode, waiting: MarkSet)]
}

offer(point, image I, marks M):
    previous = union(bucket.waiting for bucket in point.buckets)
    next = []
    for (J, N) in point.buckets:
        keep(next, J, N - M)
        overlap = N intersect M
        if overlap is not empty:
            keep(next, unionImages(J, I), overlap) // Once for this bucket.
    keep(next, I, M - previous)
    point.buckets = mergeEqualImages(next)        // Union their mark sets.
    requestFromPool(point.ticket, M - previous)   // Existing global protocol.

answer(point, marks A):
    detach (image, waiting intersect A) from every bucket
    remove A from the live buckets; remove empty buckets/point
    // Complete detachment before any callback, as today.
    for (image, marks) in detached:
        for T in marks:
            resumeExistingScalarPipeline(point.key, image, T)
```

`keep` omits empty masks. Equal image identity is a fast path. Distinct roots
can merge only after a checked equality test; a hash alone is insufficient.
Use the same pending-image component for physical points and local-boundary
requests, while keeping their different continuation keys and resume routes.

The exact invariant is:

```text
old pending image for T
    = image in the unique bucket whose waiting set contains T
```

The partition update preserves this equality for every T: an offered T gets
the old image union I; an unoffered T keeps its old image; a new T gets I.
An answer detaches exactly that image before resumption. Coalescing equal
images changes no mark's image. The number of buckets is at most the number
of pending marks; old image versions are not retained as append-only history.

Do not replace the buckets with one union image and one union mark set:

```text
offer(image for x, {T})
offer(image for y, {U})

required: T resumes x; U resumes y
incorrect Cartesian product: T and U both resume x and y
```

For the common hot-field case, one image has `{T1, ..., T221}`. A new image
for that complete mask then needs one image union, rather than 221 unions.
If every mark has a different image, the representation falls back to one
bucket per mark. Scalar concrete propagation after an answer stays unchanged.

### Select waiting readers when a mark arrives

Today, a fresh supplied mark causes `groupWrite` to scan every pending point
for that field and test its wanted set. Add a reverse index for named fields:

```text
field.waiters[T] = packed set of pending point IDs

new supply A:
    candidates = union(field.waiters[T] for T in newly answered A)
    for point in candidates:
        selected = point.wanted intersect A
        close selected memberships
        emit the existing PointReady(point, selected)
```

The index names owners and tickets; it does not own mutable image state.
Dense IDs or a sparse bitmap avoid a separate object for each membership.
Closing an answer removes the index memberships before delivery. A later
request can register again, as today. Class-marker requests keep their current
separate route.

This removes scans of unrelated readers. Its query cost is the bitmap union
cost plus the selected readers. It cannot remove delivery to distinct readers
that actually need the arriving mark. If nearly every reader wants that mark,
the selected fanout remains necessary. For SYS's many unanswered marks, image
sharing matters more than accelerating answers which have not occurred.

### Limits, unchanged behavior and validation

The 2,827,665 wrappers alone use **45,242,640 shallow bytes**. Most retain only
their own 16 bytes. Bucket storage can also remove per-mark hash entries and
unions, but those counts do not prove a multi-gigabyte saving. The global
static service itself retains about **57.46 MB** in this heap. Other large
owners, including call subscriptions and method inputs, remain important.

Keep the current three-set writer protocol, canonical field answers, FULL
mark identity, field transfer, layers, exclusions, protection, static-write
supply timing, post-statement storage and summary publication. Do not merge
different point keys. Do not discard a request because its field currently
has no writer: rules or a later write can still supply it. Do not infer that
the existing edge store can recreate an arbitrary call-stage continuation.

Before implementation, prove the bucket invariant against the scalar store
and test split masks, duplicate offers, growing images, partial answers,
reentrant requests and late supplies. Then repeat Thingsboard with the same
configuration. Record bucket/mark counts, image-union calls, selected versus
scanned readers, retained bytes, findings and latest reached iteration. This
will distinguish a useful storage reduction from a complete OOM solution.

The heap counts and exact write evidence are in the preceding report and
[memory data](data/bidirectional-run11-thingsboard-memory-20261109.json.gz).
