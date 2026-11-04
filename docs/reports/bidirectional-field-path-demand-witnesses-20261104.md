# Field-path growth: actual demand and shorter NORMAL relations

4 November 2026. Runtime: `52f32dd437d438aec4a700a02c18d94c31d58093`.
This is an investigation. The analyzer implementation is unchanged.

The data shows three distinct effects:

1. Modeled copies produce families of field paths. Demand admits many of
   these paths through broad selectors and loop repeat admissions. Admission
   does not prove that a sink requires each full path.
2. Shorter NORMAL relations do exist. In the Stirling run-5 diagnostic,
   919 of 1,220 NORMAL uniform-taint output memberships have a covering
   shorter output under the same complete premise and control interface.
   The scalar reference accepts this coverage. The packed FLOW store misses
   its proper-prefix cell.
3. Loop restriction depends on the stored relation's lengths. Two saved
   relations can produce the same backward fact but get different growth
   classifications. Thus redundant geometry can also affect whether the
   loop gate runs. Removing rows needs a check of this complete pipeline.

These findings support a concrete reduction target. They do not establish
that every growing relation is redundant, or give a measured speedup.

## 1. Runs, data, and limits

The original performance campaign reached these iterations:

| Project | Latest reached | Latest completed | Latest accepted report |
| --- | --- | --- | --- |
| Stirling-PDF | run-9 | run-8 | run-7 |
| Conductor | run-6 | run-5 | run-5 |

The [previous report](bidirectional-stirling-conductor-frontier-growth-20261104.md)
contains the complete-run counters and times. This investigation adds native
AP probes and one bounded Stirling store capture. All use the measured
runtime. No alternative analyzer configuration was tested.

The Stirling diagnostic uses FULL, 16 GiB, aliases and statics enabled, and
the same `1,1,2,...` limit schedule. It adds loopback JDWP and changes output
paths. It reached **run-8**, completed **run-7**, and accepted **run-7**.
It stopped after the requested captures. Breakpoints invalidate performance
comparisons. The diagnostic stores are evidence of actual relations, but are
not exact snapshots of the earlier performance process.

| Diagnostic committed barrier | Complete collections / expected | Current public and block summaries | Indexed saved records |
| --- | ---: | --- | --- |
| run-5 | 35 / 35 | Complete | Complete, both directions |
| run-6 | 13 / 35 | Complete | Not captured |
| run-7 | 9 / 35 | Complete | Not captured |

All 48 omitted collections have explicit whole-collection DROP records. A
field-read budget caused these drops. Missing data is unknown, not empty.
Instruction stores had already been released at the barrier. The capture
therefore does not contain the producer history of every stored relation.

Counts also vary between the two processes. Diagnostic outgoing demand in
runs 5/6/7 is 2,044 / 8,556 / 4,030. The original campaign has
1,957 / 8,792 / 4,346. Variation starts before the first breakpoint; this
investigation does not isolate its scheduling cause. The diagnostic's
`reports=22` is a sink count, not a demand count. The percentages below refer
to the diagnostic inventory only.

Portable data:

- [Full Stirling store inventory](data/bidirectional-stirling-decoder-store-inventory-20261104.json):
  raw and decoded DAGs, field and mark catalogs, exact scope/port metadata,
  controls, source pins, collection limits and cleanup receipts.
- [Coverage census and native probes](data/bidirectional-field-path-native-coverage-20261104.json):
  actual relation candidates, exclusions, test outputs and interpretation limits.
- [Conductor trace audit](data/bidirectional-conductor-relational-coverage-20261104.json):
  exact complete offered premises, inputs, relations, results and consumer labels.

The first Stirling reader attempt failed on a `ConcurrentHashMap.TreeBin`
and produced no usable inventories. Its failure and controls are preserved.
The corrected external reader follows the tree-bin chain. No analyzer code
was changed. All diagnostic processes have stopped.

## 2. Notation

`N` means NORMAL. `D` means DEMAND. `MUST` means `[any-taint]`, the native
uniform-taint tail. `FLOW` is the abstract mark slot. It is not a concrete
mark or a new mark group. `mx` is the set of excluded marks. `E` is the set
of excluded fields. `*` preserves suffix correlation. It must not be read
as a uniform-taint assertion.

An edge is shown as `premise -> conclusion [layer]`. Comparisons below keep
the complete premise, direction, method context, block entry and exit fixed
unless a section explicitly changes one of them. A field path membership
is one leaf of a packed packet. Membership counts are not packet counts,
summary-key counts, application counts or normalized handoff counts.

## 3. Stirling: the real writer and reader pattern

The hot context is:

```text
EmlProcessingUtils.decodeMimeHeader(String)
context: arg(0) == java.lang.StringBuilder
```

The actual source has this structure. This is an excerpt, not a new test
with predefined summaries:

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

The models copy both whole positions and positions such as
`CharSequence.<rule-storage>`, `Matcher.group`, `Matcher.input`,
`String.content` and `String.bytes`. These are model positions. They are
not all literal Java field reads and writes in this loop.

For example, the StringBuilder append model has both `arg0 -> this` and
`arg0 -> this.CharSequence.<rule-storage>`. Matcher group models have both
`this -> result` and `this.group -> result`. When alias analysis unifies
these endpoints, a root copy and a field copy can form a model-state cycle.
Repeated composition can add fields without a new explicit nested Java
field access. Section 7 explains the source contract and its limits.

This is a copy/read cycle over modeled state. It is not evidence of a
source rule that assigns every long field chain and a sink rule that checks
each same chain. Most measured work is FLOW. The decoder's processed
packets in the original runs 5–7 are all FLOW, and its ND and Target callback
counts are zero.

### 3.1 Exact forward and backward demand exists

The complete run-5 input public demand contains this pair. It comes from
the preceding backward run:

```text
run-5 input, collection-6, demand row 29:
  Dc = arg0.Matcher.group.[any] / FLOW, E={}, mx={}
  Dp = ret.String.content.*     / FLOW, E={}, mx={}
```

The complete run-5 outgoing public demand contains:

```text
run-5 output, collection-11, demand row 0; input to backward run-6:
  Dc = ret.String.content.[any] / FLOW, E={}, mx={}
  Dp = arg0.Matcher.group.[any] / FLOW, E={}, mx={}
```

These are stored paired rows, not reconstructed C2 answers. Thus both
directions really have demand. But the rows contain ANY and FLOW. They do
not request one concrete mark on one exact long path. ANY admits refinements
at many different next fields. C5 bounds each selected result relative to
its paired output selector; it does not bound the number of distinct
prefixes. Other rows have deeper paired selectors.

It is important to separate two checks:

```text
repeat admission:
    can this fact produce an initial for another loop-body analysis?  // C2

summary publication:
    does the whole edge satisfy one paired entry/exit demand?          // C5
```

A positive first check does not prove that this particular path reaches
a sink. Even successful C5 admission proves compatibility with a retained
approximate pair, not that every field in the raw candidate was necessary.

### 3.2 Exact shorter NORMAL outputs are present

This public run-5 row has complete premise ID 2402:

```text
P = arg0.Matcher.group.MUST / FLOW, E={}, mx={}

P -> ret.String.content.MUST                         N
P -> ret.String.content.String.<string-bytes>.MUST   N
P -> ret.String.content.Matcher.group.MUST           N
P -> ret.String.content.CharSequence.<rule-storage>.MUST N
... other descendants ...
```

All shown conclusions have `E={}` and the same `mx={75,76}`. These IDs are
the full marks for the `jjwt-hs256` and `jjwt-none-alg` rules in this capture.
The result remains FLOW for the other marks. No protection flag is present.

The same packed NORMAL row has 33 output leaves: three shorter outputs
(`ret.String.content`, `ret.CharSequence.<rule-storage>`, `ret.String.bytes`)
and ten one-field descendants under each. The ten fields include model
storage fields, array element and `File.uri`. The data contains these
combinations; it does not prove that they describe valid Java heap paths.

For this fixed premise and interface, the shorter MUST output covers the
descendant MUST output under the existing scalar rule. Root uniform taint
already includes uniform taint below an admitted field. A new cross-premise
heuristic is not needed to establish this specific fact-containment cell.

### 3.3 How much shorter-output coverage exists?

| Complete run-5 diagnostic inventory | MUST output memberships | Covered by a proper-prefix MUST output with the same complete premise |
| --- | ---: | ---: |
| Current public plus four scoped summary collections | 1,220 | 919 (75.33%) |
| Current public subset | 182 | 166 (91.21%) |
| Current loop repeat interface, block 2 / entry 80 / exit 80 | 721 | 556 (77.12%) |
| Indexed saved NORMAL records for the constrained context, both directions | 1,330 | 1,057 (79.47%) |

The last row is the post-run-5 saved inventory available to run-6. It is not
the current-summary count. Historical native record deltas are deduplicated
by semantic membership for this table. The analysis preserves field/mark
exclusions and ports. It uses literal full-atom inclusion as a sufficient
mark-mask check; it does not assume that distinct group/full IDs are equal.

The complete current run-7 summary inventory shows the same pattern:
2,830 of 3,490 MUST output memberships (81.09%) have such a shorter output.
Its post-run-7 indexed record inventory was not captured, so this is not a
count of records selected in backward run-8.

### 3.4 There are also shorter DEMAND outputs

The same `P` from section 3.2 has a DEMAND ANY row at
`ret.String.content`, `ret.CharSequence.<rule-storage>` and `ret.String.bytes`,
plus descendants. A shorter NORMAL MUST result and a longer DEMAND ANY
result are a further candidate. They are not covered by the current scalar
law: that law keeps layers and these tails distinct.

More directly, many same-layer DEMAND ANY descendants already have a proper
ANY ancestor under the same complete premise:

| Current diagnostic run | DEMAND ANY output memberships | Have a covering proper ANY prefix |
| --- | ---: | ---: |
| run-5 | 1,164 | 591 |
| run-6 | 7,795 | 3,294 |
| run-7 | 2,879 | 1,180 |

In run-6, 3,004 of these descendants coexist with their ancestor in the
same packed packet. These are actual redundant geometries under the scalar
same-layer ANY coverage rule. They are not 3,004 distinct summaries that
must be removed.

`FlowGroup.add` subtracts an arriving tree against stored trees. It does
not inherently minimize ancestor/descendant leaves inside that arriving
tree, or always remove older descendants when a broader ancestor arrives.
The snapshot proves coexistence. It does not reveal arrival order.

Only 152 / 1,164 run-5 D-ANY memberships and 388 / 2,879 run-7 memberships
have same-premise NORMAL-MUST spatial candidates. This different count
must not be confused with the stronger same-layer ANY coverage above.

## 4. A second gap: redundant rows change the loop growth decision

This exact saved pair is present at the run-5 barrier, in native record
object 166435. Its interface is loop block 2, entry 80, exit 80:

```text
P = var23.Matcher.pattern.Pattern.regex.MUST / FLOW

S: P -> var18.CharSequence.<rule-storage>.MUST                         N
L: P -> var18.CharSequence.<rule-storage>.String.<string-bytes>.MUST   N

P: E={}, mx={}
S and L output: E={}, mx={75,76}
```

The stored premise has two fields. The short output has one field; the
long output has two. S covers L as a fixed-premise MUST output.

The native backward views are:

```text
S^-1: var18.CharSequence.<rule-storage>.* / FLOW
          -> var23.Matcher.pattern.Pattern.regex.[any] / FLOW, D

L^-1: var18.CharSequence.<rule-storage>.String.<string-bytes>.* / FLOW
          -> var23.Matcher.pattern.Pattern.regex.[any] / FLOW, D
```

FLOW MUST reversal returns an uncorrelated ANY result at the old premise.
It does not append the matched suffix to that result.

An external native AP probe used this geometry and legal offered input
`var18.CharSequence.<rule-storage>.[any]/FLOW`, D. Both views produce the
same full result and preserve the same caller premise. The probe renames
the two excluded full atoms bijectively to fixture atoms T/U; it does not
claim to rehydrate every snapshot object.

But the current loop classifier gives:

```text
S^-1: output FL 2 > input FL 1  => growing     => query loop consumers
L^-1: output FL 2 = input FL 2  => not growing => bypass loop restriction
```

This is not just a theoretical tail case. The complete saved inventory has
456 covered long MUST memberships with this classification split. Each
has a covering shorter row with empty field exclusions and equal full mark
exclusions. Eighty have an original premise of length two, all at the loop
repeat interface. The actual run-6 current inventory also contains 115
distinct ANY full originals at this interface, including the offered
`var18.CharSequence.<rule-storage>.[any]` and root `var18.[any]` forms.

This proves that the ingredients coexist, and that native application can
produce equal results with different gate classifications. It does not
identify which record generated each of run-6's millions of instruction
packets. The capture has no per-result producer history.

The design issue is precise: progress based only on the stored relation's
field lengths is not invariant under this relation coverage. A longer,
redundant reader can avoid the gate that its shorter covering reader must use.
Deleting the reader can therefore change loop behavior under the current
algorithm. This part needs an explicit design and proof before removal.

## 5. Conductor: some shorter NORMAL rows are duplicates; the main writers differ

The existing bounded backward run-4 trace covers
`ParametersUtils.replace(Map, DocumentContext, String)` with a HashMap
argument context. It reached run-4, completed run-3, and accepted run-3.
It contains 4,096 events from a 0.304-second prefix. It is not a full inventory.

### 5.1 An exact native duplicate

Child loop scope is block 2, entry 40, exit 7. All these facts are FLOW,
with empty field/mark exclusions and no protection:

```text
full caller premise P = ret.MapValue.*
actual F              = var9.MapValue.*, N

seq 2329: S = var9.*          -> var3.*,          N
          result = var3.MapValue.*, N
seq 2332: completion fresh=true

seq 2435: L = var9.MapValue.* -> var3.MapValue.*, N
          result = var3.MapValue.*, N
seq 2438: completion fresh=false
```

The same pair appears at exit 40. The exits remain separate. L adds the
same field suffix on both sides, so it is a restriction of S on concrete
suffix coordinates. The trace has 20 such geometric candidates: 12 have
exact NORMAL-input/result duplicate witnesses, and eight are inverse views.
All 20 longer relations are non-growing.

The stores key FLOW rows by exact premise. They do not factor a relation
such as `a.f.* -> b.f.*` under `a.* -> b.*`. Deduplication rejects the
second caller result after native application and routing have occurred.

### 5.2 The main growing relations are not these duplicates

Of 339 captured growing applications, 324 have:

```text
I = var9.*
O = var3.<one modeled field>.*
```

There are nine added output prefixes, with 36 applications per prefix.
Root identity does not cover these relations. For example:

```text
actual var9.MapValue.*

var9.* -> var3.*                   gives var3.MapValue.*
var9.* -> var3.Iterable.Element.*  gives var3.Iterable.Element.MapValue.*
```

The second relation adds a real modeled prefix. Removing it under identity
would lose that correlation. The captured copy/read bridge also includes:

```text
seq 2605, NORMAL inverse view:
  var9.MapValue.* -> var3.Iterator.Element.Map.Entry.Value.*
  actual var9.MapValue.*, N; full P=ret.MapValue.*
seq 2606:
  result var3.Iterator.Element.Map.Entry.Value.*, N; growing=true
```

The source reads map entries, recurses through maps and lists, and writes
`result.put` / `replacedList.add`. These models add and remove collection
prefixes. The trace does not map every local or relation to its exact
producing instruction. It does establish a different pattern from Stirling's
large fixed-premise MUST redundancy.

### 5.3 Most sampled loop support is repeat-only

The trace has 393 loop observations. All have two repeat admissions and
zero enclosing results. Of these, 376 (95.67%) also have no adjacent
admission. For the bridge above, repeat C2 returns:

```text
var3.Iterator.Element.*                       N
var3.Iterator.Element.Map.Entry.Value.*       N
```

Thus the gate retains this growing result for another body pass. It has
not shown a sink or enclosing exit consumer for this result. These are
answers from the frozen previous demand, not newly invented demand in the
same run. A repeat-only result can reach a useful consumer after more
iterations. The data does not justify deleting all repeat-only paths.

## 6. Why a broader prefix heuristic is not enough

The native AP probes establish these controls:

| Relations and actual input | Result |
| --- | --- |
| `p.* -> q.*` and `p.f.* -> q.f.*`; actual `p.f.g.$/T`, N | Both produce `q.f.g.$/T`, N |
| Same relations; actual `p.*/FLOW`, N | Short produces `q.*/FLOW`, N; long produces `q.f.[any]/FLOW`, D |
| `p.* -> q.*` and `p.f.* -> q.*`; actual `p.f.g.$/T`, N | Results differ: `q.f.g.$/T` and `q.g.$/T` |
| Short output excludes T, or its field exclusion rejects f | It cannot replace an otherwise matching nonexcluding long output |

The second row does not disprove concrete suffix-relation inclusion. It
shows that native abstract annotations and consumer observations differ.
The loop observer uses exact patterns, layers, protection and control labels;
it does not quotient all of them by scalar AP coverage.

There is also a reverse exclusion control. A NORMAL root MUST result with
`E={h}` can cover a descendant `f.MUST` with empty E when `f != h`. But its
reverse query can fail on a root STAR actual with incomparable `E={g}`,
while the descendant reverse query succeeds. Native execution confirms this.
Forward fact containment alone is not a complete backward replacement proof.

### 6.1 Which inside case is necessary?

A follow-up native driver probe gives a counterexample to removing all
`inside` matching. It does not establish a need for the ancestor STAR/FLOW
case in the table above. The required input here is concrete uniform taint.

```java
void main() {
    Box x = sourceAllT();
    Object y = helper(x);
    sinkU(y);
}

Object helper(Box p) {
    Object t = p.f;
    return transform(t);
}
```

Rules: `sourceAllT` assigns `T` to `ret.[any-taint]`; `transform` checks
`CM(arg0.$,T)` and assigns `U` to `ret.$`; `sinkU` checks `CM(arg0.$,U)`.
The marks differ, so a plain T copy or an alias cannot produce U.

The current production driver uses only the finite code/rule/call forms.
No predefined or injected summary is used. It completes and accepts
**run-3**, with field limits `1,1,2`, FULL mode and one worker:

```text
run-1 helper:
    p.*/T -> p.*/T             D  // concrete request answer
    p.*/T -> t.[any]/T         D  // field read consumes unknown suffix
    p.*/T -> ret.$/U           D  // conditional source

run-2 helper:
    demand: Dc=ret.$/U, Dp=p.*/T
    actual submitted requirement: ret.$/U, N
    ret.$/U -> t.$/T           N  // reverse conditional source
    ret.$/U -> p.f.$/T         N  // reverse field read; saved native record

run-3 helper call:
    current local demand: empty
    actual input: p.[any-taint]/T, N
    saved run-2 record read forward: p.f.$/T -> ret.$/U, N
    applicable=false; inside=true
    result: ret.$/U, N -> caller y.$/U, N -> NormalTarget
```

The saved record is generated by the actual backward run. The broader
MUST input guarantees T at `p.f`, so its use is definite and the U result
is NORMAL. An `applicable`-only test rejects it: a point premise does not
cover the whole uniform input. With no helper demand, current analysis
cannot replace the rejected replay. The other matching saved forward
record is argument identity; it does not produce U.

The [portable probe evidence](data/bidirectional-inside-policy-counterexample-20261104.json)
contains the full source, commands, source/bytecode pins and complete output.
It checks the current complete driver and the exact native replay step.
It does not claim a whole-engine mutant run with `inside` removed.
The compiler and probe JVM have stopped. Analyzer implementation is unchanged.

### 6.2 A non-MUST counterexample: field cuts followed by field reads

A second probe establishes a necessary MAY case. It also checks the complete
driver with an external matcher mutant. No MUST facts occur in its trace.

```java
void main() {
    Box x = sourceABF();
    Object y = helper(x.a.b);
    sinkU(y);
}

Object helper(Box p) {
    Object t = p.f;
    return transform(t);
}
```

`sourceABF` assigns T only to `ret.a.b.f.$`. It does not assign uniform taint.
`transform` and `sinkU` have the rules from section 6.1. The finite program
lowers the argument read `x.a.b` into the call binding. It removes fields;
it does not violate the non-growing binding-in condition.

The run-1 helper summary and the saved run-2 helper record are the same as
in section 6.1. They are generated by actual execution, not injected:

```text
run-1: p.*/T -> ret.$/U, D
run-2: ret.$/U -> p.f.$/T, N
run-3 helper demand: empty
```

The field limit and the argument read create the key MAY input:

```text
run-3, limit 2:
    source:                 ZERO -> x.a.b.f.$/T
    after field cut:        ZERO -> x.a.b.[any]/T   D
    bind argument x.a.b:    ZERO -> p.[any]/T       D

    saved helper view:      p.f.$/T -> ret.$/U      N
    applicable=false; inside=true
    result:                 ZERO -> y.$/U          D
    sink:                   ZERO -> DemandTarget   D

run-4, limit 3:
    saved helper relation returns requirement p.f.$/T
    reverse argument binding gives x.a.b.f.$/T without a cut
    source discharge retains the source permission and Target guidance

run-5, limit 4:
    source:                 ZERO -> x.a.b.f.$/T    N
    bind argument x.a.b:    ZERO -> p.f.$/T         N
    saved helper view:      p.f.$/T -> ret.$/U      N
    applicable=true
    result:                 ZERO -> y.$/U          N
    sink:                   ZERO -> NormalTarget   N
```

The monotonic global limit does not prevent a shorter input. Reading
`x.a.b` consumes the entire known prefix of the cut fact, leaving MAY at
the helper root. This is why comparing the record's premise depth with the
new global limit is insufficient.

Results of the complete fixture driver, FULL, one worker, limits `1,1,2,3,4`:

| Matcher | run-3 outgoing demand | run-3 Target demand | Latest reached / completed / accepted | Final findings |
| --- | ---: | ---: | --- | ---: |
| Current | 1 | 1 | run-5 / run-5 / run-5 | 1 |
| External mutant, non-MUST inside disabled | 0 | 0 | run-3 / run-3 / run-3 | 0 |

The mutant keeps MUST matching and ordinary micro transfers. It rejects
the saved helper application on the MAY input. No helper demand remains
to cause reanalysis. The Target disappears, and the driver stops before
the field path becomes precise. The current driver reports the real U sink.

The [portable evidence](data/bidirectional-non-must-inside-counterexample-20261104.json)
contains the full program, current and mutant matcher source, both manifests,
complete traces and bytecode/source hashes. Class-loading evidence confirms
that the mutant runs from an external class directory. No repository analyzer
source, build output or test source was changed. Both JVMs completed.

This proves a need for MAY `inside` under the current saved-record and demand
protocol. It does not establish a need for an ancestor STAR/FLOW input. That
remaining cell must be evaluated separately.

## 7. Where the modeled combinations can come from

The source and model audit gives a plausible alias route for the unusual
StringBuilder context. A caller builds a StringBuilder, calls `toString`,
then passes that string through `safeMimeDecode` and `trim` to the decoder.
The models use broad copies for `toString` and `trim`.

The alias adapter converts `CopyAllMarks` into an external assignment. DSU
alias analysis merges its endpoints. Rule conditions do not restrict this
alias merge. `taintCopyOnly` is declared in serialized rules but is not carried
to the resolved `TaintPassThrough`. `Matcher.group` uses this flag in its
model. The call resolver can use an exact alias allocation type without
checking compatibility with the declared String type.

These behaviors can connect string, matcher and builder model positions.
They are a source-backed route, not a captured runtime alias proof for
every field in section 3. Similar CopyAllMarks-to-alias behavior exists in
the old base-only branch. It is not established as a new regression here.
Do not remove model fields merely because their type names look unusual.

## 8. What to change next, and what still needs proof

The strongest first target is **canonical output coverage under one complete
premise and control interface**:

```text
same P, scope, exit, direction, layer and compatible headers:
    retain a covering MUST prefix instead of its covered MUST descendants;
    remove ANY descendants already covered by an ANY ancestor;
    also minimize redundant leaves inside one arriving packed tree.
```

The MUST prefix law already exists in `Reference.subsumes`. Native probes
confirm the store/reference disagreement in eligible cells and preserve
the exclusion controls. This can reduce the set of values that gets replayed
or observed, rather than only make each query faster. The measured coverage
fractions describe the available reduction in those inventories, not a
predicted reduction in total engine time.

Two associated contracts must be explicit before implementation:

1. **Loop progress and consumer observations.** Coverage must not depend on
   a redundant row bypassing the growing-result gate. Equivalent retained
   outputs must also have compatible observation/continuation behavior.
2. **Both record directions.** A saved NORMAL record is read in both
   directions. Preserve its matching domains, exclusions and exact ports;
   do not prove only forward containment.

Cross-premise suffix factoring is a separate target. It has real duplicate
examples in Conductor, but does not cover that trace's main prefix-adding
writers. Cross-layer NORMAL-MUST versus DEMAND-ANY removal is another
separate target. It changes the present demand contract and needs a new
proof. Neither change is included silently in this investigation.

The current evidence does not prove a unique sink ancestry for every long
path. To close that remaining causal question, a later selected experiment
should trace the retained relation's producer and paired demand through the
loop gate, then compare the canonical and original output sets. It must
measure actual replay, repeat admission, C5 output and instruction work.
No further analyzer experiment or runtime change was made here.

## 9. Relevant implementation points

- [Scalar coverage and native MUST reversal](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Reference.kt):
  `subsumes`, `mustRecordReadView`.
- [Packed FLOW admission](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Groups.kt):
  `FlowGroup.add`, `subtractSubsumed`; descendant coverage uses `Tail.ANY` only.
- [Loop gate and exact observed facts](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/LoopOutputRestriction.kt):
  `loopSummaryGrows`, `LoopObservedFacts`, `restrictWithCertificate`.
- [Complete consumer query](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/LoopConsumerObservation.kt):
  adjacent/repeat C2 and saved-replay/enclosing C5 are separate families.

Validation: native AP controls and the snapshot decoder controls pass. Portable
artifact hashes and JSON decode checks are recorded with the data. The
production/rules source pins did not change. No core test result or new
performance result is claimed for a documentation-only investigation.
