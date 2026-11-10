# OWASP helper demand cycle from run-7

10 November 2026. Runtime: `14d7b63369d94f49d4c551be8405ed7719f267cc`.
The latest reached, completed and accepted forward iteration is **run-11**.
The stop reason is `RUN_LIMIT`. Production source is unchanged.

The selected method is
`org.owasp.benchmark.testcode.BenchmarkTest01000$Test#doSomething(HttpServletRequest, String)`.
It has one captured method key, with context `[{}]`, and no loop decomposition.

The trace identifies two different populations. Some outgoing DEMAND rows are
new cuts of NORMAL relations which a persisted NORMAL relation already covers.
Other rows are already DEMAND before restriction. The second population must
not be deleted merely because the first population is redundant.

## Reading the trace

Each run below contains all incoming paired demand rows, all submitted C2
facts, the complete emitted initial family for each submitted fact, and every
scalar leaf of the final NORMAL and DEMAND summary store. No field family is
omitted. Identical offers are grouped with their observed multiplicity.
An initial is an identity start. `$` FLOW initials are shown before summary
normalization; summary storage replaces their `$` tails with `*`.

The names are exact field labels, not interchangeable fields:

| Trace name | Native accessor |
| --- | --- |
| `bytes` | `String#<string-bytes>` model field |
| `javaBytes` | `String#bytes` |
| `content` | `CharSequence#content` |
| `[]` | Array element accessor; serialized name `*`, not a STAR tail |

`N` means NORMAL; `D` means DEMAND. All emitted initials in this capture are
NORMAL FLOW. All shown exclusions and protection sets are empty. The marks are:

```text
T1 = java/security/sqli.yaml:sql-injection#source#0;0;$UNTRUSTED;1
T2 = java/security/sqli.yaml:sql-injection#source#1;0;$UNTRUSTED;2
```

A row under "incoming demand" is `(entry D_c -> exit D_p)` in the current
run's direction. It is the preceding run's outgoing DEMAND summary reversed.
The normal summaries listed below are produced in this run. Saved NORMAL
records are a separate retained family, used by the coverage checks later.
The data attachment contains that complete saved family too.

| Run | Direction | Field limit | Incoming paired rows | C2 offers | Returned initial memberships | Distinct initial keys/layers | Final NORMAL leaves | Final DEMAND leaves |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| run-7 | FORWARD | 6 | 4 | 16 | 20 | 14 | 12 | 6 |
| run-8 | BACKWARD | 7 | 6 | 14 | 24 | 5 | 9 | 8 |
| run-9 | FORWARD | 8 | 8 | 16 | 20 | 14 | 16 | 6 |
| run-10 | BACKWARD | 9 | 6 | 14 | 24 | 5 | 9 | 8 |
| run-11 | FORWARD | 10 | 8 | 16 | 20 | 14 | 16 | 6 |

Summary leaf counts differ from packed packet counts. For example, run-8 has
seven final packets containing nine NORMAL leaves and eight DEMAND leaves.
A returned C2 membership is an admission result, not proof that the method
executes that initial twice; entry storage still deduplicates repeated starts.

## Complete run traces

### run-7: forward, field limit 6

```java
// Incoming demand, D_c -> D_p:
//   param.bytes.[].[any]/FLOW -> ret.content.*/FLOW
//   param.bytes.[any]/FLOW -> ret.*/FLOW
//   param.javaBytes.[].[any]/FLOW -> ret.content.*/FLOW
//   param.javaBytes.[any]/FLOW -> ret.*/FLOW
//
// Submitted facts -> all emitted initials:
//   param.[any-taint]/T1/N (1 offer)
//     -> param.javaBytes.[any-taint]/FLOW/N, param.javaBytes.[].[any-taint]/FLOW/N, param.bytes.[any-taint]/FLOW/N, param.bytes.[].[any-taint]/FLOW/N
//   param.$/T1/N (1 offer)
//     -> NONE
//   param.javaBytes.[].$/T1/N (1 offer)
//     -> param.javaBytes.[].*/FLOW/N, param.javaBytes.$/FLOW/N, param.javaBytes.[].$/FLOW/N
//   param.javaBytes.content.$/T1/N (1 offer)
//     -> param.javaBytes.content.*/FLOW/N, param.javaBytes.$/FLOW/N
//   param.javaBytes.$/T1/N (1 offer)
//     -> param.javaBytes.$/FLOW/N
//   param.javaBytes.*/FLOW/N (1 offer)
//     -> param.javaBytes.*/FLOW/N
//   param.javaBytes.*/T1/D (1 offer)
//     -> param.javaBytes.*/FLOW/N
//   param.bytes.[].$/T1/N (1 offer)
//     -> param.bytes.[].*/FLOW/N, param.bytes.$/FLOW/N, param.bytes.[].$/FLOW/N
//   param.bytes.content.$/T1/N (1 offer)
//     -> param.bytes.content.*/FLOW/N, param.bytes.$/FLOW/N
//   param.bytes.$/T1/N (1 offer)
//     -> param.bytes.$/FLOW/N
//   param.bytes.*/FLOW/N (1 offer)
//     -> param.bytes.*/FLOW/N
//   param.bytes.*/T1/D (1 offer)
//     -> param.bytes.*/FLOW/N
//   param.content.$/T1/N (1 offer)
//     -> NONE
//   param.content.*/FLOW/N (1 offer)
//     -> NONE
//   param.content.*/T1/D (1 offer)
//     -> NONE
//   param.$/FLOW/N (1 offer)
//     -> NONE
String doSomething(HttpServletRequest request, String param) {
    String bar = "";
    if (param != null) {
        bar = new String(Base64.decodeBase64(
                Base64.encodeBase64(param.getBytes())));
    }
    return bar;
}
// Produced NORMAL summaries:
//   param.bytes.*/FLOW -> ret.*/FLOW
//   param.bytes.*/FLOW -> ret.bytes.*/FLOW
//   param.bytes.*/FLOW -> ret.javaBytes.*/FLOW
//   param.bytes.[].*/FLOW -> ret.*/FLOW
//   param.bytes.[].[any-taint]/FLOW -> ret.content.[any-taint]/FLOW
//   param.bytes.[any-taint]/FLOW -> ret.[any-taint]/FLOW
//   param.javaBytes.*/FLOW -> ret.*/FLOW
//   param.javaBytes.*/FLOW -> ret.bytes.*/FLOW
//   param.javaBytes.*/FLOW -> ret.javaBytes.*/FLOW
//   param.javaBytes.[].*/FLOW -> ret.*/FLOW
//   param.javaBytes.[].[any-taint]/FLOW -> ret.content.[any-taint]/FLOW
//   param.javaBytes.[any-taint]/FLOW -> ret.[any-taint]/FLOW
// Produced DEMAND summaries:
//   param.bytes.*/FLOW -> ret.[any]/FLOW
//   param.bytes.[].*/FLOW -> ret.bytes.[any]/FLOW
//   param.bytes.[].*/FLOW -> ret.javaBytes.[any]/FLOW
//   param.javaBytes.*/FLOW -> ret.[any]/FLOW
//   param.javaBytes.[].*/FLOW -> ret.bytes.[any]/FLOW
//   param.javaBytes.[].*/FLOW -> ret.javaBytes.[any]/FLOW
```

### run-8: backward, field limit 7

```java
// Incoming demand, D_c -> D_p:
//   ret.[any]/FLOW -> param.bytes.*/FLOW
//   ret.[any]/FLOW -> param.javaBytes.*/FLOW
//   ret.bytes.[any]/FLOW -> param.bytes.[].*/FLOW
//   ret.bytes.[any]/FLOW -> param.javaBytes.[].*/FLOW
//   ret.javaBytes.[any]/FLOW -> param.bytes.[].*/FLOW
//   ret.javaBytes.[any]/FLOW -> param.javaBytes.[].*/FLOW
//
// Submitted facts -> all emitted initials:
//   ZERO/N (2 offers)
//     -> NONE
//   ret.[any]/T1/D (2 offers)
//     -> ret.*/FLOW/N, ret.javaBytes.*/FLOW/N, ret.bytes.*/FLOW/N
//   ret.[any]/T2/D (2 offers)
//     -> ret.*/FLOW/N, ret.javaBytes.*/FLOW/N, ret.bytes.*/FLOW/N
//   ret.$/T1/N (2 offers)
//     -> ret.$/FLOW/N
//   ret.content.$/T1/N (2 offers)
//     -> ret.content.*/FLOW/N, ret.$/FLOW/N
//   ret.$/T2/N (2 offers)
//     -> ret.$/FLOW/N
//   ret.content.$/T2/N (2 offers)
//     -> ret.content.*/FLOW/N, ret.$/FLOW/N
String doSomething(HttpServletRequest request, String param) {
    String bar = "";
    if (param != null) {
        bar = new String(Base64.decodeBase64(
                Base64.encodeBase64(param.getBytes())));
    }
    return bar;
}
// Produced NORMAL summaries:
//   ret.*/FLOW -> param.*/FLOW
//   ret.*/FLOW -> param.bytes.*/FLOW
//   ret.*/FLOW -> param.bytes.[].*/FLOW
//   ret.*/FLOW -> param.javaBytes.*/FLOW
//   ret.*/FLOW -> param.javaBytes.[].*/FLOW
//   ret.bytes.*/FLOW -> param.*/FLOW
//   ret.bytes.*/FLOW -> param.javaBytes.*/FLOW
//   ret.javaBytes.*/FLOW -> param.*/FLOW
//   ret.javaBytes.*/FLOW -> param.bytes.*/FLOW
// Produced DEMAND summaries:
//   ret.*/FLOW -> param.bytes.[any]/FLOW
//   ret.*/FLOW -> param.javaBytes.[any]/FLOW
//   ret.bytes.*/FLOW -> param.bytes.[].[any]/FLOW
//   ret.bytes.*/FLOW -> param.javaBytes.[].[any]/FLOW
//   ret.content.*/FLOW -> param.bytes.[].[any]/FLOW
//   ret.content.*/FLOW -> param.javaBytes.[].[any]/FLOW
//   ret.javaBytes.*/FLOW -> param.bytes.[].[any]/FLOW
//   ret.javaBytes.*/FLOW -> param.javaBytes.[].[any]/FLOW
```

### run-9: forward, field limit 8

```java
// Incoming demand, D_c -> D_p:
//   param.bytes.[].[any]/FLOW -> ret.bytes.*/FLOW
//   param.bytes.[].[any]/FLOW -> ret.content.*/FLOW
//   param.bytes.[].[any]/FLOW -> ret.javaBytes.*/FLOW
//   param.bytes.[any]/FLOW -> ret.*/FLOW
//   param.javaBytes.[].[any]/FLOW -> ret.bytes.*/FLOW
//   param.javaBytes.[].[any]/FLOW -> ret.content.*/FLOW
//   param.javaBytes.[].[any]/FLOW -> ret.javaBytes.*/FLOW
//   param.javaBytes.[any]/FLOW -> ret.*/FLOW
//
// Submitted facts -> all emitted initials:
//   param.[any-taint]/T1/N (1 offer)
//     -> param.javaBytes.[any-taint]/FLOW/N, param.javaBytes.[].[any-taint]/FLOW/N, param.bytes.[any-taint]/FLOW/N, param.bytes.[].[any-taint]/FLOW/N
//   param.$/T1/N (1 offer)
//     -> NONE
//   param.javaBytes.[].$/T1/N (1 offer)
//     -> param.javaBytes.[].*/FLOW/N, param.javaBytes.$/FLOW/N, param.javaBytes.[].$/FLOW/N
//   param.javaBytes.content.$/T1/N (1 offer)
//     -> param.javaBytes.content.*/FLOW/N, param.javaBytes.$/FLOW/N
//   param.javaBytes.$/T1/N (1 offer)
//     -> param.javaBytes.$/FLOW/N
//   param.javaBytes.*/FLOW/N (1 offer)
//     -> param.javaBytes.*/FLOW/N
//   param.javaBytes.*/T1/D (1 offer)
//     -> param.javaBytes.*/FLOW/N
//   param.bytes.[].$/T1/N (1 offer)
//     -> param.bytes.[].*/FLOW/N, param.bytes.$/FLOW/N, param.bytes.[].$/FLOW/N
//   param.bytes.content.$/T1/N (1 offer)
//     -> param.bytes.content.*/FLOW/N, param.bytes.$/FLOW/N
//   param.bytes.$/T1/N (1 offer)
//     -> param.bytes.$/FLOW/N
//   param.bytes.*/FLOW/N (1 offer)
//     -> param.bytes.*/FLOW/N
//   param.bytes.*/T1/D (1 offer)
//     -> param.bytes.*/FLOW/N
//   param.content.$/T1/N (1 offer)
//     -> NONE
//   param.content.*/FLOW/N (1 offer)
//     -> NONE
//   param.content.*/T1/D (1 offer)
//     -> NONE
//   param.$/FLOW/N (1 offer)
//     -> NONE
String doSomething(HttpServletRequest request, String param) {
    String bar = "";
    if (param != null) {
        bar = new String(Base64.decodeBase64(
                Base64.encodeBase64(param.getBytes())));
    }
    return bar;
}
// Produced NORMAL summaries:
//   param.bytes.*/FLOW -> ret.*/FLOW
//   param.bytes.*/FLOW -> ret.bytes.*/FLOW
//   param.bytes.*/FLOW -> ret.javaBytes.*/FLOW
//   param.bytes.[].*/FLOW -> ret.*/FLOW
//   param.bytes.[].[any-taint]/FLOW -> ret.bytes.[any-taint]/FLOW
//   param.bytes.[].[any-taint]/FLOW -> ret.content.[any-taint]/FLOW
//   param.bytes.[].[any-taint]/FLOW -> ret.javaBytes.[any-taint]/FLOW
//   param.bytes.[any-taint]/FLOW -> ret.[any-taint]/FLOW
//   param.javaBytes.*/FLOW -> ret.*/FLOW
//   param.javaBytes.*/FLOW -> ret.bytes.*/FLOW
//   param.javaBytes.*/FLOW -> ret.javaBytes.*/FLOW
//   param.javaBytes.[].*/FLOW -> ret.*/FLOW
//   param.javaBytes.[].[any-taint]/FLOW -> ret.bytes.[any-taint]/FLOW
//   param.javaBytes.[].[any-taint]/FLOW -> ret.content.[any-taint]/FLOW
//   param.javaBytes.[].[any-taint]/FLOW -> ret.javaBytes.[any-taint]/FLOW
//   param.javaBytes.[any-taint]/FLOW -> ret.[any-taint]/FLOW
// Produced DEMAND summaries:
//   param.bytes.*/FLOW -> ret.[any]/FLOW
//   param.bytes.[].*/FLOW -> ret.bytes.[any]/FLOW
//   param.bytes.[].*/FLOW -> ret.javaBytes.[any]/FLOW
//   param.javaBytes.*/FLOW -> ret.[any]/FLOW
//   param.javaBytes.[].*/FLOW -> ret.bytes.[any]/FLOW
//   param.javaBytes.[].*/FLOW -> ret.javaBytes.[any]/FLOW
```

### run-10: backward, field limit 9

```java
// Incoming demand, D_c -> D_p:
//   ret.[any]/FLOW -> param.bytes.*/FLOW
//   ret.[any]/FLOW -> param.javaBytes.*/FLOW
//   ret.bytes.[any]/FLOW -> param.bytes.[].*/FLOW
//   ret.bytes.[any]/FLOW -> param.javaBytes.[].*/FLOW
//   ret.javaBytes.[any]/FLOW -> param.bytes.[].*/FLOW
//   ret.javaBytes.[any]/FLOW -> param.javaBytes.[].*/FLOW
//
// Submitted facts -> all emitted initials:
//   ZERO/N (2 offers)
//     -> NONE
//   ret.[any]/T1/D (2 offers)
//     -> ret.*/FLOW/N, ret.javaBytes.*/FLOW/N, ret.bytes.*/FLOW/N
//   ret.[any]/T2/D (2 offers)
//     -> ret.*/FLOW/N, ret.javaBytes.*/FLOW/N, ret.bytes.*/FLOW/N
//   ret.$/T1/N (2 offers)
//     -> ret.$/FLOW/N
//   ret.content.$/T1/N (2 offers)
//     -> ret.content.*/FLOW/N, ret.$/FLOW/N
//   ret.$/T2/N (2 offers)
//     -> ret.$/FLOW/N
//   ret.content.$/T2/N (2 offers)
//     -> ret.content.*/FLOW/N, ret.$/FLOW/N
String doSomething(HttpServletRequest request, String param) {
    String bar = "";
    if (param != null) {
        bar = new String(Base64.decodeBase64(
                Base64.encodeBase64(param.getBytes())));
    }
    return bar;
}
// Produced NORMAL summaries:
//   ret.*/FLOW -> param.*/FLOW
//   ret.*/FLOW -> param.bytes.*/FLOW
//   ret.*/FLOW -> param.bytes.[].*/FLOW
//   ret.*/FLOW -> param.javaBytes.*/FLOW
//   ret.*/FLOW -> param.javaBytes.[].*/FLOW
//   ret.bytes.*/FLOW -> param.*/FLOW
//   ret.bytes.*/FLOW -> param.javaBytes.*/FLOW
//   ret.javaBytes.*/FLOW -> param.*/FLOW
//   ret.javaBytes.*/FLOW -> param.bytes.*/FLOW
// Produced DEMAND summaries:
//   ret.*/FLOW -> param.bytes.[any]/FLOW
//   ret.*/FLOW -> param.javaBytes.[any]/FLOW
//   ret.bytes.*/FLOW -> param.bytes.[].[any]/FLOW
//   ret.bytes.*/FLOW -> param.javaBytes.[].[any]/FLOW
//   ret.content.*/FLOW -> param.bytes.[].[any]/FLOW
//   ret.content.*/FLOW -> param.javaBytes.[].[any]/FLOW
//   ret.javaBytes.*/FLOW -> param.bytes.[].[any]/FLOW
//   ret.javaBytes.*/FLOW -> param.javaBytes.[].[any]/FLOW
```

### run-11: forward, field limit 10

```java
// Incoming demand, D_c -> D_p:
//   param.bytes.[].[any]/FLOW -> ret.bytes.*/FLOW
//   param.bytes.[].[any]/FLOW -> ret.content.*/FLOW
//   param.bytes.[].[any]/FLOW -> ret.javaBytes.*/FLOW
//   param.bytes.[any]/FLOW -> ret.*/FLOW
//   param.javaBytes.[].[any]/FLOW -> ret.bytes.*/FLOW
//   param.javaBytes.[].[any]/FLOW -> ret.content.*/FLOW
//   param.javaBytes.[].[any]/FLOW -> ret.javaBytes.*/FLOW
//   param.javaBytes.[any]/FLOW -> ret.*/FLOW
//
// Submitted facts -> all emitted initials:
//   param.[any-taint]/T1/N (1 offer)
//     -> param.javaBytes.[any-taint]/FLOW/N, param.javaBytes.[].[any-taint]/FLOW/N, param.bytes.[any-taint]/FLOW/N, param.bytes.[].[any-taint]/FLOW/N
//   param.$/T1/N (1 offer)
//     -> NONE
//   param.javaBytes.[].$/T1/N (1 offer)
//     -> param.javaBytes.[].*/FLOW/N, param.javaBytes.$/FLOW/N, param.javaBytes.[].$/FLOW/N
//   param.javaBytes.content.$/T1/N (1 offer)
//     -> param.javaBytes.content.*/FLOW/N, param.javaBytes.$/FLOW/N
//   param.javaBytes.$/T1/N (1 offer)
//     -> param.javaBytes.$/FLOW/N
//   param.javaBytes.*/FLOW/N (1 offer)
//     -> param.javaBytes.*/FLOW/N
//   param.javaBytes.*/T1/D (1 offer)
//     -> param.javaBytes.*/FLOW/N
//   param.bytes.[].$/T1/N (1 offer)
//     -> param.bytes.[].*/FLOW/N, param.bytes.$/FLOW/N, param.bytes.[].$/FLOW/N
//   param.bytes.content.$/T1/N (1 offer)
//     -> param.bytes.content.*/FLOW/N, param.bytes.$/FLOW/N
//   param.bytes.$/T1/N (1 offer)
//     -> param.bytes.$/FLOW/N
//   param.bytes.*/FLOW/N (1 offer)
//     -> param.bytes.*/FLOW/N
//   param.bytes.*/T1/D (1 offer)
//     -> param.bytes.*/FLOW/N
//   param.content.$/T1/N (1 offer)
//     -> NONE
//   param.content.*/FLOW/N (1 offer)
//     -> NONE
//   param.content.*/T1/D (1 offer)
//     -> NONE
//   param.$/FLOW/N (1 offer)
//     -> NONE
String doSomething(HttpServletRequest request, String param) {
    String bar = "";
    if (param != null) {
        bar = new String(Base64.decodeBase64(
                Base64.encodeBase64(param.getBytes())));
    }
    return bar;
}
// Produced NORMAL summaries:
//   param.bytes.*/FLOW -> ret.*/FLOW
//   param.bytes.*/FLOW -> ret.bytes.*/FLOW
//   param.bytes.*/FLOW -> ret.javaBytes.*/FLOW
//   param.bytes.[].*/FLOW -> ret.*/FLOW
//   param.bytes.[].[any-taint]/FLOW -> ret.bytes.[any-taint]/FLOW
//   param.bytes.[].[any-taint]/FLOW -> ret.content.[any-taint]/FLOW
//   param.bytes.[].[any-taint]/FLOW -> ret.javaBytes.[any-taint]/FLOW
//   param.bytes.[any-taint]/FLOW -> ret.[any-taint]/FLOW
//   param.javaBytes.*/FLOW -> ret.*/FLOW
//   param.javaBytes.*/FLOW -> ret.bytes.*/FLOW
//   param.javaBytes.*/FLOW -> ret.javaBytes.*/FLOW
//   param.javaBytes.[].*/FLOW -> ret.*/FLOW
//   param.javaBytes.[].[any-taint]/FLOW -> ret.bytes.[any-taint]/FLOW
//   param.javaBytes.[].[any-taint]/FLOW -> ret.content.[any-taint]/FLOW
//   param.javaBytes.[].[any-taint]/FLOW -> ret.javaBytes.[any-taint]/FLOW
//   param.javaBytes.[any-taint]/FLOW -> ret.[any-taint]/FLOW
// Produced DEMAND summaries:
//   param.bytes.*/FLOW -> ret.[any]/FLOW
//   param.bytes.[].*/FLOW -> ret.bytes.[any]/FLOW
//   param.bytes.[].*/FLOW -> ret.javaBytes.[any]/FLOW
//   param.javaBytes.*/FLOW -> ret.[any]/FLOW
//   param.javaBytes.[].*/FLOW -> ret.bytes.[any]/FLOW
//   param.javaBytes.[].*/FLOW -> ret.javaBytes.[any]/FLOW
```

## The repeated pattern

The incoming demand set for run-9 equals that for run-11. Their C2 input
families, emitted initial families and final summaries are also equal. The
same holds between run-8 and run-10. Run-7 already has the six forward demand
rows. Run-9 adds four NORMAL MUST relations and reaches the later forward
family. This is a method-local two-direction cycle, not a proof that the whole
engine has reached a fixed point.

The root MAY input in the backward direction is important:

```text
run-8 and run-10:
  demand:    ret.bytes.[any]/FLOW
  submitted: ret.[any]/T1, DEMAND
  initial:   ret.bytes.*/FLOW, NORMAL
```

The incoming MAY contains the demanded field. C2 therefore admits the same
shallow FLOW initial on each backward pass. The larger global field limit
alone cannot settle this pattern.

### Population A: C5 cuts a known NORMAL specialization

The classification is performed on the exact NORMAL relation before the cut.
It does not compare an arbitrary MAY demand with a superficially similar
NORMAL conclusion.

A forward same-field example has this already persisted provider:

```text
S: param.*/FLOW -> ret.*/FLOW, NORMAL
```

For suffix `bytes.[]`, S already gives exactly:

```text
R: param.bytes.[].*/FLOW -> ret.bytes.[].*/FLOW, NORMAL
```

C5 nevertheless processes R against the shallower paired row:

```text
D_c = param.bytes.[any]/FLOW
D_p = ret.*/FLOW
budget = FL(D_p) + 1 = 1

cut R -> param.bytes.[].*/FLOW -> ret.bytes.[any]/FLOW, DEMAND
```

The aligned-relation subsumption runs after C5 admission and accepts NORMAL
STAR/FLOW candidates. The cut is now ANY/DEMAND, so this test cannot recognize
its covered NORMAL origin. The current run store also does not combine its
candidate basis with the persisted record store before this cut.

The backward example is equally specific:

```text
persisted S: ret.*/FLOW -> param.bytes.[].*/FLOW, NORMAL
suffix:     bytes

specialized R:
  ret.bytes.*/FLOW -> param.bytes.[].bytes.*/FLOW, NORMAL

paired row:
  D_c = ret.[any]/FLOW
  D_p = param.bytes.*/FLOW
  budget = 2

cut result:
  ret.bytes.*/FLOW -> param.bytes.[].[any]/FLOW, DEMAND
```

All exact cut families and one persisted provider for each are listed below.
`R` is the NORMAL selected value immediately before field limiting.

| Runs | R | Persisted NORMAL provider | Input/output suffix | Cut demand |
| --- | --- | --- | --- | --- |
| 7, 9, 11 | `param.bytes.[].*/FLOW -> ret.bytes.[].*/FLOW` | `param.*/FLOW -> ret.*/FLOW` | `bytes.[]` | `param.bytes.[].*/FLOW -> ret.bytes.[any]/FLOW` |
| 7, 9, 11 | `param.javaBytes.[].*/FLOW -> ret.bytes.[].*/FLOW` | `param.javaBytes.*/FLOW -> ret.bytes.*/FLOW` | `[]` | `param.javaBytes.[].*/FLOW -> ret.bytes.[any]/FLOW` |
| 7, 9, 11 | `param.bytes.[].*/FLOW -> ret.javaBytes.[].*/FLOW` | `param.bytes.*/FLOW -> ret.javaBytes.*/FLOW` | `[]` | `param.bytes.[].*/FLOW -> ret.javaBytes.[any]/FLOW` |
| 7, 9, 11 | `param.javaBytes.[].*/FLOW -> ret.javaBytes.[].*/FLOW` | `param.*/FLOW -> ret.*/FLOW` | `javaBytes.[]` | `param.javaBytes.[].*/FLOW -> ret.javaBytes.[any]/FLOW` |
| 8, 10 | `ret.content.*/FLOW -> param.bytes.[].content.*/FLOW` | `ret.*/FLOW -> param.bytes.[].*/FLOW` | `content` | `ret.content.*/FLOW -> param.bytes.[].[any]/FLOW` |
| 8, 10 | `ret.bytes.*/FLOW -> param.bytes.[].bytes.*/FLOW` | `ret.*/FLOW -> param.bytes.[].*/FLOW` | `bytes` | `ret.bytes.*/FLOW -> param.bytes.[].[any]/FLOW` |
| 8, 10 | `ret.javaBytes.*/FLOW -> param.bytes.[].javaBytes.*/FLOW` | `ret.*/FLOW -> param.bytes.[].*/FLOW` | `javaBytes` | `ret.javaBytes.*/FLOW -> param.bytes.[].[any]/FLOW` |
| 8, 10 | `ret.content.*/FLOW -> param.javaBytes.[].content.*/FLOW` | `ret.*/FLOW -> param.javaBytes.[].*/FLOW` | `content` | `ret.content.*/FLOW -> param.javaBytes.[].[any]/FLOW` |
| 8, 10 | `ret.bytes.*/FLOW -> param.javaBytes.[].bytes.*/FLOW` | `ret.*/FLOW -> param.javaBytes.[].*/FLOW` | `bytes` | `ret.bytes.*/FLOW -> param.javaBytes.[].[any]/FLOW` |
| 8, 10 | `ret.javaBytes.*/FLOW -> param.javaBytes.[].javaBytes.*/FLOW` | `ret.*/FLOW -> param.javaBytes.[].*/FLOW` | `javaBytes` | `ret.javaBytes.*/FLOW -> param.javaBytes.[].[any]/FLOW` |

Every observed producer of these ten demand families passes this test; none
of them requires attributing an already-DEMAND producer to a NORMAL one.
The providers exist before the respective run, so their existence does not
depend on candidate arrival order inside the current method.

A precise detector for this measured scope is:

```text
on C5 result before field limiting:
    require R is NORMAL STAR/FLOW on both ends
    require the selected row would cut at least one output path
    find an independently retained NORMAL provider S in this method/scope
    find suffix sigma such that:
        R.premise.path    = S.premise.path    + sigma
        R.conclusion.path = S.conclusion.path + sigma
    require matching bases and marks; preserve the E/mx conditions
    if all tests pass:
        classify this cut as a covered specialization
```

For this capture E and mx are empty. The checked source rule is
`specializeNormalFlow` / `removeAlignedFlowCovered` in `AlignedFlowRelations.kt`.
MUST, concrete marks, protection and nonempty exclusions need their existing
separate rules. A longer output alone is not a sufficient coverage test.
For example, `param.bytes.* -> ret.*` does not cover
`param.bytes.[].* -> ret.bytes.[].*`: adding `[]` to the first relation yields
`ret.[].*`, not `ret.bytes.[].*`. The same-field forward witness in the table
uses the saved `param.* -> ret.*` relation instead.

The witness is constructive: for every residual suffix tau, both R and S map
`S.premise.sigma.tau` to `S.conclusion.sigma.tau`. Their opposite-direction
STAR/FLOW reads preserve the same alignment. Saved summaries are replayed
before current-demand admission, so the provider does not need the removed
cut row to become applicable. This establishes the duplicated relation. A
production change must also prove that all affected handoff/source permission
routes remain covered; the detector alone is not that implementation proof.
There is no need to restore an unrestricted-candidate archive to identify it.
The exact current C5 value and retained NORMAL basis provide the witness.

### Population B: already-MAY before C5

The remaining rows are:

```text
forward, every run 7/9/11:
  param.bytes.*     -> ret.[any]          / FLOW, DEMAND
  param.javaBytes.* -> ret.[any]          / FLOW, DEMAND

backward, every run 8/10:
  ret.* -> param.bytes.[any]              / FLOW, DEMAND
  ret.* -> param.javaBytes.[any]          / FLOW, DEMAND
```

These rows already have their shown MAY/DEMAND shape before field limiting.
Their paths fit their effective C5 budgets. C5 does not introduce their
uncertainty. A NORMAL `param.bytes.* -> ret.*` has correlated suffixes;
`param.bytes.* -> ret.[any]` does not. The aligned NORMAL test above cannot
remove the latter by treating `*` as MAY.

The first observed DEMAND output for the representative STAR premise is at
the String constructor, in both directions. These are actual processed inputs
and post-statement outputs from run-7 and run-8:

```text
IR names:
  %2 = param.getBytes()
  %3 = Base64.encodeBase64(%2)
  %4 = Base64.decodeBase64(%3)
  %1 = the new String object

run-7, origin param.bytes.*/FLOW:
  param.getBytes():          param.bytes.* / N -> %2.* / N
  encodeBase64():            %2.* / N          -> %3.* / N
  decodeBase64():            %3.* / N          -> %4.* / N
  %1.<init>(%4), inst6:      %4.* / N          -> %1.[any] / D
  bar = %1:                 %1.[any] / D      -> bar.[any] / D
  return bar:               bar.[any] / D     -> ret.[any] / D

run-8, origin ret.*/FLOW:
  reverse return:           ret.* / N         -> bar.* / N
  reverse bar = %1:         bar.* / N         -> %1.* / N
  %1.<init>(%4), inst6:      %1.* / N          -> %4.[any] / D
  reverse decodeBase64():   %4.[any] / D      -> %3.[any] / D
  reverse encodeBase64():   %3.[any] / D      -> %2.[any] / D
  reverse param.getBytes(): %2.[any] / D      -> param.bytes.[any] / D
```

Every fact in this block has mark FLOW. The block shows the MAY-producing
route. The same constructor also emits the separate NORMAL STAR routes
listed in the complete run trace. A normal output and a demand output can
come from the same processed input.

The constructor model in `model/java/config/stdlib/java-lang.yaml` includes:

```text
arg(0).*    -> this.bytes.* / FLOW
arg(0).[].* -> this.*       / FLOW
```

`JIRRuleForms.pass` makes ordinary micro-edges from these copy actions. The
second action reads an element from an abstract array STAR in the forward
direction. Reversing the first action reads `bytes` from an abstract receiver
STAR in the backward direction. Neither STAR input names that child path.
The ancestor branch of `EdgeApplication.flow` emits ANY/DEMAND for such an
ordinary field read. This is separate from the restriction on inside matching
of saved summary records. The dynamic trace pins the first output to this
constructor; the model and transfer code explain its geometry. The observer
does not record the individual bound action ID.

Consequently, the root cycle is:

```text
run-7 output:
  param.bytes.* -> ret.[any], DEMAND

run-8 incoming demand:
  ret.[any] -> param.bytes.*
  submitted ret.[any]/T1, DEMAND -> initial ret.*/FLOW, NORMAL

run-8 output, after the constructor route above:
  ret.* -> param.bytes.[any], DEMAND

run-9 incoming demand:
  param.bytes.[any] -> ret.*
  submitted param.bytes.*/FLOW, NORMAL -> initial param.bytes.*/FLOW, NORMAL

run-9 output:
  param.bytes.* -> ret.[any], DEMAND
```

The `javaBytes` family takes the parallel route. No growing field chain is
needed for this cycle. Each handoff changes a shallow MAY conclusion into an
entry selector; C2 emits STAR; the constructor creates MAY again. The effective
budgets are sufficient for these paths. Increasing the limit cannot remove
this source of uncertainty.

This gives an exact second diagnostic category: a pre-C5 MAY output, created
by an ordinary ancestor field read, whose reversed handoff is re-admitted to
the same STAR start. It does not prove that the MAY relation is dispensable.
The NORMAL STAR alternative preserves suffix correlation; the MAY route loses
it. A new rule to settle this cycle must justify removing that uncertainty.
Do not attribute this route to the helper's saved MUST reversal alone.

| Completed runs | Total outgoing DATA demand leaves | Cut NORMAL specializations with saved providers | Already-MAY before C5 |
| --- | ---: | ---: | ---: |
| run-7 / run-9 / run-11 | 6 each | 4 each | 2 each |
| run-8 / run-10 | 8 each | 6 each | 2 each |

Removing only Population A would leave two DATA demand rows in either direction.
This helper has no current Target or ZERO demand row in these runs. OWASP also
has Target demand in other methods. This local diagnosis is not permission to
stop the whole analyzer or to discard all intrinsic MAY relations.

## Evidence and validation

The same execution supplies every run table. It retains FULL mode, aliases
and statics, the `1,1,2,...` schedule, 8g and the 1000 s timeout. It finishes
run-11 with `RUN_LIMIT`. The attached receipts state the exact finding
comparison and observer record count. Timings from an instrumented execution
are not substituted into the performance report.

The final capture has **2,414 records and zero observer errors**. Its 2,633
exact rule/location identities match the preceding accepted capture, with
zero missing or new findings. It has 2,633 confirmed findings and zero
provisional findings. An intermediate instruction probe used the wrong index
accessor and failed. Its statement records are not used. The corrected probe
reads `instruction.location.index`; all tables above use this final execution.

The [data record](data/bidirectional-owasp-helper-cycle-20261110.json) embeds
all scalar run tables, each C2 query and returned initial family, exact C5
producer classifications, persisted NORMAL witnesses, launch configuration,
observer/analysis source and completion receipts. The
[complete native trace](data/bidirectional-owasp-helper-cycle-20261110.jsonl.gz)
retains the original packets and accessor/mark catalogs.
