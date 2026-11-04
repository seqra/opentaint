# Stirling-PDF and Conductor: demand growth and iteration cost

4 November 2026. Read-only investigation of the existing
`52f32dd437d438aec4a700a02c18d94c31d58093` campaign. No new analyzer run,
alternative configuration or runtime change is included.

Latest reached / completed / accepted report:

- Stirling-PDF: **run-9 / run-8 / run-7**, timeout in run-9.
- Conductor: **run-6 / run-5 / run-5**, timeout in run-6.

The demand increase is concentrated in a few existing methods and mostly in
FLOW field-path relations. The time increase has two different causes:
physical path expansion, and repeated summary/consumer queries over those
paths. It is not explained by the frontier row count alone.

The [portable evidence](data/bidirectional-stirling-conductor-frontier-growth-20261104.json)
contains full relevant per-method demand maps, source/log hashes, exact
operation counters, depth histograms and bounded geometry samples. The
[campaign report](bidirectional-loop-demand-trie-performance-20261104.md)
has timings, quality results and CPU/allocation evidence.

## 1. What the demand count measures

`HandOff` counts successful normalized builder insertions. The frontier
includes **both public method and scoped block DATA/control demand**. It is
not a root-only count. `DemandStore` entry/pair statistics also include blocks.
There is no missing-block-count explanation for these results.

The count is not the number of submitted facts, instructions, native matches,
summary applications or consumer queries. One demand row can admit several
new field prefixes and be applied to many actual inputs. One admitted initial
can have many paired output demands. Both dimensions matter.

The selected refinement policy does not require row counts to decrease as
field limits increase. C2 can refine one ANY selector to several different
first-field initials. C5 retains the matching pair and bounds its output by
`min(currentLimit, FL(Dp)+1)`. This limits each result's depth. It does not
limit the number of distinct prefixes, paired relations or applications.

FLOW annotations, concrete memberships and normalized handoff rows have
different units. Do not add the census columns below to reconstruct a frontier.

## 2. Stirling: where the extra demand comes from

| Run | Direction / limit | Incoming demand | Outgoing demand | Outgoing method keys | Engine s |
| --- | --- | ---: | ---: | ---: | ---: |
| run-3 | FORWARD / 2 | 274,935 | 1,436 | 146 | 5.252 |
| run-4 | BACKWARD / 3 | 1,436 | 3,155 | 116 | 3.199 |
| run-5 | FORWARD / 4 | 3,155 | 1,957 | 87 | 7.209 |
| run-6 | BACKWARD / 5 | 1,957 | 8,792 | 60 | 43.479 |
| run-7 | FORWARD / 6 | 8,792 | 4,346 | 57 | 221.182 |
| run-8 | BACKWARD / 7 | 4,346 | 18,971 | 57 | 260.877 |

Run-5 reduces its immediate input by 38.0%; run-7 by 50.6%. Comparing run-3,
run-5 and run-7 changes the input relation and the field limit. The backward
runs between them expand the finer field-path relations.

### One existing decoder dominates the increase

The exact logged context is:

```text
stirling.software.common.util.EmlProcessingUtils#decodeMimeHeader(java.lang.String)
[{arg(0) == java.lang.StringBuilder}]
```

The declaration takes String. Preserve the logged context; it is not a Java
argument-type proof.

| Outgoing frontier | run-3 | run-5 | run-7 |
| --- | ---: | ---: | ---: |
| Decoder | 339 | 960 | 3,057 |
| All other methods | 1,097 | 997 | 1,289 |
| Total | 1,436 | 1,957 | 4,346 |

The decoder adds 621 rows in the first comparison, while all other methods
lose 100. It then adds 2,097 of the next net increase of 2,389: **87.8%**.
No new printed method key appears in either forward comparison. The method
sets shrink. More methods or contexts do not explain this growth.

### The increase is mainly scoped FLOW

| Forward run | Outgoing FLOW annotations | Block subset | Public subset | Concrete memberships | Protected memberships | Target rows |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| run-3 | 1,347 | 850 | 497 | 204 | 11 | 137 |
| run-5 | 1,981 | 1,361 | 620 | 113 | 0 | 105 |
| run-7 | 4,444 | 3,416 | 1,028 | 86 | 0 | 103 |

Public counts are total minus block subset. Blocks account for 83.4% of the
extra FLOW annotations from run-5 to run-7. Concrete, protected and Target
counts decrease. All processed decoder packets in runs 5–7 are FLOW. Its ND
combination and Target callback counters are zero.

The decoder keeps four layout blocks, one loop and six entry scopes. New
loop decomposition or more entry scopes do not explain the increase either.

### Actual field patterns

The source at `EmlProcessingUtils.java:492–556` has this structure:

```java
String decodeMimeHeader(String encodedText) {
    StringBuilder result = new StringBuilder();
    String processedText = /* regex replacement */;
    Matcher matcher = /* matcher for processedText */;
    while (matcher.find()) {
        result.append(processedText, lastEnd, matcher.start());
        String encodedValue = matcher.group(3);
        String decodedValue = /* Base64 or quoted-printable decode */;
        result.append(decodedValue); // fallback branches also append
        lastEnd = matcher.end();
    }
    result.append(processedText.substring(lastEnd));
    return result.toString();
}
```

The actual modeled AP vocabulary includes `Matcher.group`, `Matcher.input`,
`String.content`, `String.bytes`, string-byte storage and CharSequence rule
storage. The regex and StringBuilder models contain multi-field copies and
copies to both root and storage positions. These are analysis/model fields,
not a list of literal Java field operations in the method.

Observed geometry examples:

```text
run-6 processed NORMAL EXACT FLOW, depth5:
  <local>.Matcher.group.Matcher.group.String.bytes
         .Matcher.group.String.<string-bytes>.$ / FLOW
  original: var(18).String.<string-bytes>.$ / FLOW

run-7 candidate DEMAND ANY FLOW, depth6:
  <argument>.Matcher.group.String.content.String.content
            .Matcher.group.String.content.Matcher.group.[any] / FLOW
  original: var(23).Matcher.group.Matcher.pattern.Pattern.regex.[any] / FLOW
```

The geometry snapshots omit the output local/argument index and some packet
metadata. They are not full annotated causal traces. Their exhaustive depth
histograms, however, establish that the processed packet count is real.

One actual run-5 C5 sample has `Dp = ret.CS.CS.[any]/FLOW`, with
`CS = CharSequence.<rule-storage>`. Its budget is three. A selected first
branch `ret.CS.CS.CS.String.bytes.String.content.[any]/FLOW` at depth five is
cut to `ret.CS.CS.CS.[any]/FLOW`. A run-3 sample with empty-path Dp has budget
one. This is a composed query candidate before C5 restriction, not evidence
that a depth-five fact was stored under run-5's global limit four.
Longer paired selectors therefore retain more distinct prefix shapes.
The rule is working at the selected per-row depth bound; that bound does
not collapse every alternative into one row.

This is evidence of modeled field-path expansion. It does not prove that
every such path is required, or that any particular model is incorrect.

## 3. Stirling: why 7 s becomes 43 s and then 221 s

The same decoder is expensive for different reasons in the two directions.

| Decoder operation | run-5 F | run-6 B | run-7 F |
| --- | ---: | ---: | ---: |
| Processed instruction packets | 17,545 | 2,229,737 | 79,332 |
| Fresh post-statement packets | 27,334 | 2,532,736 | 119,625 |
| Loop baseline scalar checks | 206,470 | 470,087 | 5,982,903 |
| Baseline plus trial observations | 365,961 | 691,413 | 9,760,126 |
| Saved-record selections | 1,926,479 | 2,793,831 | 70,331,846 |
| Saved reverse views | 813,268 | 1,529,772 | 27,048,619 |
| Native C2 lookups | 407,731 | 619,804 | 12,139,085 |
| Prepared C5 queries | 716,844 | 3,517,269 | 28,382,885 |

**Run-6 has physical FLOW path expansion.** The decoder processes 127.1 times
as many packets as in run-5 and accounts for 98.05% of all processed packets.
Of its packets, 72.26% have the maximum field length five; 99.96% occur at
instructions in the original cyclic CFG component. This does not mean the
decomposition left an unhandled CFG cycle: the counters use original CFG
component labels.

The global field limit bounds depth, while intermediate transfer, caller
application and publication can still enumerate many paths before C5. The
growth-only loop gate also has native bypasses for Reach/non-growing rows.
Its aggregate bypass counter does not identify each bypass geometry; it
cannot prove that those rows alone caused the expansion.

**Run-7 has much more pure consumer-query work.** It processes 28.1 times
fewer decoder instruction packets than run-6, yet takes 5.09 times as long.
The observer checks adjacent and repeat admissions, applies selected saved
relations, and intersects resulting enclosing summaries with demand. Prefix
trials repeat those operations.

Relative to run-5, physical decoder packets rise 4.52 times, observations
26.67 times, saved selections 36.51 times and prepared C5 queries 39.59 times.
The decoder accounts for 99.57% of global prepared C5 queries in run-7.
The profile agrees: the loop observer is 82.90% of sampled Java work in
run-7, versus 40.91% in run-6. These are Java sample shares, not wall seconds.

The gate rejects 2,779,549 run-7 decoder scalars, or 46.46%, **after** their
baseline observation. Completion deduplication also occurs after the gate.
A small final frontier does not refund that work. Saved-record counts include
actual replay and pure observation; 70.33 million selections do not mean
70.33 million stored records or successful propagations.

This is not a wholesale fallback: decoder prepared/native reference fallback
counters are zero. High plan hit counts do not cache the answer for an actual
fact. They reuse eligible output programs; actual scalar selection, AP
application, packing, field cuts and observation unions still execute.

## 4. Conductor: where demand grows

| Run | Direction / limit | Incoming demand | Outgoing demand | Outgoing method keys | Engine s |
| --- | --- | ---: | ---: | ---: | ---: |
| run-3 | FORWARD / 2 | 238,762 | 46,632 | 661 | 26.052 |
| run-4 | BACKWARD / 3 | 46,632 | 130,791 | 442 | 277.610 |
| run-5 | FORWARD / 4 | 130,791 | 220,052 | 413 | 130.704 |

Run-5 is slower than run-3 but faster than run-4. Demand volume and time do
not move together even within these three runs.

| Existing method context | run-3 outgoing | run-4 outgoing | run-5 outgoing |
| --- | ---: | ---: | ---: |
| `ParametersUtils.replace` | 599 | 42,162 | 13,612 |
| `ParametersUtils.replaceList` | 552 | 26,159 | 24,612 |
| `ParametersUtils.replaceVariables`, four args | 1,248 | 19,357 | 10,402 |
| `WorkflowExecutorOps.decide` | 13,936 | 5,385 | 25,029 |
| `ForkJoinDynamicTaskMapper.getMappedTasks` | 2,256 | 1,432 | 18,581 |
| `DoWhile.execute` | 1,861 | 1,257 | 11,363 |

The three conversion helpers contribute 87,678 run-4 rows: **67.04%** of the
frontier. Their increase of 85,279 exceeds the total net increase of 84,159,
because other methods shrink. They recursively read and rebuild maps/lists.
Backward analysis distributes requested output paths through those copies.

Run-5 growth shifts into workflow/task processing. For example, `decide`
adds 19,644 rows and the dynamic mapper adds 17,149. Source calls connect
these methods to `getTaskInput`/`getTaskInputV2` and the conversion helpers.
This identifies the call path, not an exact ancestry trace for every new row.

Outgoing FLOW annotations increase 47,859 → 113,594 → 225,572. Their block
subsets are 26,043 → 79,771 → 129,163. Outgoing protected memberships are zero
in all three runs. Concrete memberships are 3,490 → 17,620 → 7,094. FLOW path
relations dominate; protected concrete edges do not explain the growth.

## 5. Conductor: the expensive work also changes

| Complete-run operation | run-3 | run-4 | run-5 |
| --- | ---: | ---: | ---: |
| Processed instruction packets | 1,017,665 | 1,076,822 | 2,255,164 |
| Processed at cyclic CFG points | 115,953 | 724,417 | 350,398 |
| Native C2 calls (`c2Direct`) | 948,766 | 31,907,504 | 7,685,905 |
| Demand-trie candidates | 526,499 | 51,217,319 | 5,784,201 |
| Prepared C5 eligibility occurrences checked | 6,364,045 | 3,132,470 | 43,178,661 |
| Prepared C5 queries | 882,966 | 6,688,864 | 6,602,276 |
| Prepared scalar/program candidates | 421,512 | 5,209,762 | 18,694,131 |
| C5 program-finalization/native row attempts | 2,606,026 | 14,257,109 | 321,261,307 |

Run-4 instruction packets grow only 5.8% from run-3, but native C2 grows
33.6 times. The two `replace` helpers alone perform **60,565,427 current
DATA callbacks**, 20,255,606 full observations and 30,928,742 native C2 calls.
They have 6,282 live local input groups. Their ND combination count is zero.
The [existing exact trace](bidirectional-loop-demand-trie-performance-20261104.md#5-conductor-trace-the-application-product)
shows distinct complete premises, output geometries and ports participating
in this unary application product. It does not support an exact-cache remedy:
the 339 captured growing decision keys are distinct.

Run-5 has much less helper observer work but much denser paired C5 work.
`replaceList` alone builds 48,674 plans and performs **31,562,162 eligibility
checks**, 73.10% of the global count. That is 648.4 checks per built plan,
versus about 8.68 in run-4. It has only 179 live input groups. A group count
is therefore not the number of relevant paired demand rows for each query.

Global DATA-entry index memberships grow from 5,125 in run-4 to 6,885 in
run-5, while paired rows grow from 46,632 to 130,791. The approximate density
changes from 9.10 to 19.00 pairs per entry. These ratios include control rows
in the numerator and are not exact DATA-only fanout averages.

Counts of constructed programs are cumulative work. The 22,006,634 programs
constructed across run-5 plans are not a retained inventory of 22 million
simultaneously live programs. Unique plan keys and cache-reset causes were
not measured; a global plan cache is not justified by these counts alone.

## 6. A confirmed avoidable operation: dense C5 finalization

The output trie already selects candidate program ordinals. However,
`PreparedOutputPrograms.intersect` then visits **all** programs in the
prepared plan, including programs whose selected bucket is null:

```kotlin
// Current code, simplified. Selection is already complete.
for (program in programs) {
    countRowAttempt()
    val bucket = buckets[program.ordinal]
    if (bucket == null) {
        countRejectedRow()
        continue
    }
    packAndLimit(bucket, program)
}
```

| Run | Finalization/native row attempts | Aggregate rejected attempts | Prepared scalar/program candidates |
| --- | ---: | ---: | ---: |
| Stirling run-5 | 3,657,039 | 2,547,550 | 1,172,718 |
| Stirling run-6 | 10,125,161 | 4,250,503 | 6,771,057 |
| Stirling run-7 | 275,181,352 | 243,958,020 | 32,693,514 |
| Conductor run-4 | 14,257,109 | 9,276,742 | 5,209,762 |
| Conductor run-5 | 321,261,307 | 302,575,905 | 18,694,131 |

The last reject fraction is 94.18%. **It is not a measured empty-bucket
fraction**: this counter also includes native failed row restrictions.
The logs cannot split the two exactly. It is also not evidence of 321 million
expensive geometric intersections or 321 million retained facts.

The dense scan itself is proved by the source. Draining only selected buckets
in original program order avoids that scan while retaining native packing,
protection, paired eligibility and field cuts. This is already the sparse C5
candidate in the [next proposal](../design/bidirectional-joined-writer-observer-work-next-iteration-20261104.md#4-sparse-c5-output-program-finalization).
The new counters strengthen its work-volume motivation. They do not establish
a factor-two wall-time improvement: the wider bookkeeping region is 17.32%
of sampled Java work in Conductor run-5 and includes work the change keeps.

## 7. Findings and limits

The selected depth bound works, but **bounded depth is not bounded path width,
paired-row fanout or repeated consumer work**. That is the main design limit
exposed here. A few thousand frontier rows can still cause millions of
qualified applications and tens of millions of pure checks.

There is concrete avoidable work in the dense C5 scan. There is also a large
remaining cost in repeated raw/trial consumer composition before completion
deduplication. The latter needs exact consumer/replay eligibility evidence
before removing work. High non-fresh completion counts alone do not prove
identical query keys or safe early rejection.

The evidence does not prove that every new field relation is necessary. It
also does not prove an infinite loop, a specific erroneous model, or an exact
exponential recurrence. Complete per-port row inventories, persisted NORMAL
record cardinality and full Stirling instruction-to-model provenance are not
in these captures. Treat repeated modeled string/matcher fields as the next
trace target; do not delete them or change the selected growth-only gate
without a semantic argument.

The native code and selected sources remain byte-identical to the measured
runtime. This report adds analysis and portable data only.
