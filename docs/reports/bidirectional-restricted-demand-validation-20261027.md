# Restricted demand: implementation checks

Date: 27 October 2026. Status: **implementation in progress; not accepted**.

Follow-up, 28 October: the user selected ignoring field exclusions on
abstract STAR demand. This supersedes the exclusion-union candidate in
the historical findings below. The [follow-up review](../design/bidirectional-restricted-demand-followup-20261028.md)
also explains the stale STAR validator and separates immediate writer
registration from the old pool-supply gate. No project scan has started.

The selected contract is [restricted-demand-static-closure.md](../../spec/restricted-demand-static-closure.md).
Implementation started at `d8edf2b262dec9bd3c8563aa3255d05eba43553d`.
The changes are not committed. These checks do not describe a final runtime.

No project scan has started for this iteration. The last referenced
Thingsboard campaign reached **run-2**, completed **run-1**, and accepted **run-1**.
The JVM sequence tests below exercise complete runs through **run-3**.
Unit test iterations are not project performance results.

## Behavior decisions still required

### Abstract STAR demand with field exclusions

The selected spec requires an abstract STAR entry to have empty field
exclusions. That producer invariant is false with the retained cleaners.

```java
Object adjust(Object x, Object y) {
    x.f = y;
    removeAllMarksBelow(x);
    return x;
}
```

The packed AP operations produce this trace in a later forward run:

```text
initial:          x/STAR/{}/FLOW
after write:     x/STAR/{f}/FLOW, NORMAL
after cleaner:   x/STAR/{f}/FLOW, DEMAND
after return:    ret/STAR/{f}/FLOW, DEMAND
handoff entry:   ret/STAR/{f}/FLOW
builder:         rejects the entry
```

The problem also affects the original shared initial rule. Demand
`x/STAR/{f}/FLOW` and input `x/STAR/{g}/FLOW` both cover `x.h` when f, g,
and h differ. The demand's shared initial does not satisfy that input.
The original Lean counterexample `Abs.emitW_needs_patTail` checks this
failure. Merely removing the builder check does not repair it.

A candidate keeps the shared initial when the actual input satisfies it.
For the remaining same-path STAR case, it emits STAR with the union of
the two field exclusions. It keeps FLOW as the mark. This candidate has
a constructive proof for the original scalar domain. It is not applied
to runtime code. The user has been asked to select the behavior.

### Concrete static STAR input at the next call

The retained static validator and the restored STAR demand have different
domains:

```text
actual input to A:       C.f/ANY/T
entry demand in A:       C.f/STAR/T
emitted initial:         C.f/STAR/T
start conclusion:       C.f/STAR/T, DEMAND
ordinary call A -> B:    passes the static position as is
input validator in B:    rejects STAR; accepts only EXACT/ANY
```

`StaticProducerGrammarTest` reproduces this rejection through the engine
and an ordinary call. Its passing diagnostic means that the rejection
was reproduced. It does not mean that the behavior is correct.
The user has been asked whether named-field STAR inputs, with legal
exclusions, must be accepted. Broad root/class concrete marks remain
outside the selected grammar.

### A pre-exit write can be required by a returned flow

The current post-exit-only W inventory is not sufficient:

```java
Object get(Object p) {
    C.f = p;
    return C.f;
    // NormalExit rule clears the outgoing C.f value.
}
void main() { sinkT(get(sourceT())); }
```

Run-1 has a real candidate and a reader relation `C.f -> ret`. The exit
rule kills the outgoing `p -> C.f` writer relation. The producer-effect
repair still supplies T to the earlier read. However, the handoff cannot
compose `p -> C.f -> ret` from its post-exit inventory. Run-2 derives the
body answer `ret -> p`, but its paired guide permits only `ret -> C.f`.
The next forward run loses the finding.

The driver regression confirms a run-1 candidate, complete engine runs,
and a missing final finding. This is a correctness failure, not a timing
or diagnostic-count difference. The user has been asked whether the
handoff can also use pre-exit writer relations as guidance. Such a change
has not been applied. The producer channel itself still supplies no
handoff seeds under the current selected contract.

## Exit processing and immediate write effects

Another regression test checks a requirement that the spec already states:

```java
void main() { set(sourceT()); }
void set(Object p) {
    C.f = p;
    sinkT(C.f);
    // The normal exit has a cleaner which removes static T.
}
```

The real write must supply the earlier sink even when the exit cleaner
kills the outgoing static summary. Moving the old early summary to exit
processing alone fails this test for a nonstatic input premise.

The implementation separates the pre-exit producer effect from the
post-exit summary. The producer effect uses the same actual caller input
matching and AP application as the old early writer path. It can supply
the global static pool. It cannot emit a normal summary, record, CFG
result, or new local write registration. This implements the existing
producer-immediacy requirement; it does not change field transfer or add
grounding support. The common suite checks the repair with one and two
caller levels. Both cases pass. The separate handoff gap above remains.

## Component checks

| Check | Observed result | Scope |
|---|---|---|
| JVM adapter suite | 440 tests, no failures | Fifth build; final source freeze still required |
| JVM sequence suite | 13 tests, no failures | Fixed demand, shared FLOW, records, cleaners, sources and complete conjunction guards |
| Seventh common suite | 1,963 tests, five failures | All five failures reproduce the missing pre-exit guidance; other common checks pass |
| Application suite | 1,039 tests, ten failures, 13 skipped | Eight cleaner cases have extra findings and no missing expected finding; two Spring fixtures fail during setup |
| Go suite | 1,323 tests, no failures | Seventh build |
| Spring and sequence rerun | 15 tests, no failures | Spring fixtures now declare marks, pass the joined prescan graph, and use the current schedule and report state |
| Late-exception and protocol checks | 14 tests, no failures | Eighth build; a late exceptional mark reply checks sinks without publishing a normal-exit summary |
| Frozen closure tests | 10 tests, no failures | Includes 64 call graphs against an independent eager oracle, mark pairs, cycles, ZERO, ownership and packing |
| Original restricted-demand proof models | All audits pass | Local demand, mark, closure and exit-handler contracts; no whole-JVM proof |
| Restriction protection model | Four audits pass | Preserve the protected subset during restriction; no new protection |
| Pending repair models | 30 local audits pass | Six excluded-STAR, 15 static-input-domain and nine pre-exit-guidance checks; candidates are not selected and production adapter obligations remain |

The common test updates remove assertions for discarded SQ authority.
The independent scalar oracle now uses fixed demand, the original raw
selection predicate, preserved STAR handoff, and the existing GROUP selector
relation. The static carry remains a family at the actual position; a
root probe is not stored as a universal static relation. Finding, cleaner,
source and full-guard checks remain in place. A final complete suite is
still required after the runtime is fixed and frozen.

The seven test attempts are not seven analysis iterations. Each failed
handoff case reaches and completes **run-1, run-2 and run-3**, with limits
**1, 1 and 2**. Its final accepted forward report is **run-3**, but that
report is empty and is incorrect.

| Pre-exit write/read case | Run-1 mode | Exit kills static | Final finding |
|---|---|---|---|
| Nonstatic input, local getter | GROUP | No | Present; control passes |
| Nonstatic input, two returning wrappers | GROUP | No | Present; control passes |
| Nonstatic input, local getter | FULL | No | Present; control passes |
| Nonstatic input, local getter | GROUP | Yes | Missing |
| Nonstatic input, one returning wrapper | GROUP | Yes | Missing |
| Nonstatic input, two returning wrappers | GROUP | Yes | Missing |
| Nonstatic input, local getter | FULL | Yes | Missing |
| Static copy `C.f = C.g`, local getter | GROUP | Yes | Missing |

The representative trace is:

```text
run-1: candidate present
post-exit writer: absent after the kill
run-2 incoming guide in getter:
    ret/STAR/FLOW -> C.f/STAR/FLOW
run-2 raw body answer:
    ret/STAR/FLOW -> arg(0)/STAR/FLOW, NORMAL
publication: rejected by the paired exit guide
source hits: empty
run-3: no source replay; final report empty; STOP_RULE
```

Pre-exit dependencies include both nonstatic-to-static writers and
static-to-static copies. Returning wrappers also need the correctly bound
caller dependencies. Adding only the local concrete producer-pool rows
would not close this gap. The pending behavior decision must cover the
complete guidance path.

## Campaign preparation

The saved baseline is `f945f92c5ae554ff4f5fc7696ee5a269210478bb`.
A fresh full-content check passes for all 25 input datasets and all four
project models. The table below records these results. The check did not
run the analyzer or a compiler. The baseline will not be rerun. The new scans must use Gradle `runProjectAnalyzer` and
the configured heaps and timeouts.

Cleanup removed 257 old HPROF, JFR, CPU profile and MAT index files from
the previous correlated-concrete experiment: 148,519,354,024 logical bytes.
No analyzer for that experiment was active. Logs, SARIF, inputs, source
bindings and decoded reports were kept.

The external evidence root is
`/drive-testcomp/opentaint-go-rules/restricted-demand-20261027`.
It contains the cleanup and baseline receipts, proof logs and each test
attempt. AP probe and candidate proof receipts are also under
`/drive-testcomp/opentaint-go-rules/restricted-demand-implementation-20261027`.
No performance improvement, final finding comparison, or completed
implementation is claimed by this report.

## Fixed-input content audit

The comparison uses the saved baseline content inventory. It reads every
selected file again. It compares file membership and content hashes; it
does not reuse modification-time checks as evidence. All entries below
match. The project repository is at
`bbdbcc5fd35d976d93348760ea60561e4670f68c`.

| Dataset | Files | Logical bytes read | Manifest SHA-256 |
|---|---:|---:|---|
| OWASP-class-roots-full | 4,559 | 12,465,291 | `9113ccc6c647f8287dcc1baa987a1afa67ffb732f43401ee910e0e270f40f837` |
| OWASP-dependencies | 131 | 49,262,395 | `c41fa0564b817cf1dc8c839e2decb17fe5ffb1c1de42ba9e4273bf777ed7928c` |
| OWASP-checkout-sources-full | 17,741 | 351,760,737 | `644ac49553f87fb5ec23d223d9e87e05286c02f30fc139472ca6190fe862cfed` |
| OWASP-model-sources-full | 17,741 | 351,760,737 | `644ac49553f87fb5ec23d223d9e87e05286c02f30fc139472ca6190fe862cfed` |
| OWASP-toolchain | 454 | 384,610,193 | `57275a904796f3525c13130a335ab20a80108b63dd06c408554aa319afe12562` |
| conductor-class-roots-full | 1,717 | 10,634,916 | `7351ef11a264d322f7ce12fc95fc9dd990c9156bef32a0b97bd0e4d1103e640e` |
| conductor-dependencies | 783 | 546,319,395 | `be6725bc3f2edd95c9d0412f0c2ba994a729779d9b292479035479e14e2b0053` |
| conductor-checkout-sources-full | 5,522 | 57,049,551 | `84cf102a6a809e2f2470f74c6adf0a2d32333b10794055d40e3a7c2a1c8501df` |
| conductor-model-sources-full | 5,522 | 57,049,551 | `84cf102a6a809e2f2470f74c6adf0a2d32333b10794055d40e3a7c2a1c8501df` |
| conductor-toolchain | 308 | 298,868,805 | `75981e5c2948876007fd2ba09d46bad86ebefbe39b04f49ee775eed4f190b941` |
| thingsboard-class-roots-full | 14,540 | 97,086,905 | `76be973b43f550c81a9b090ae3d81faca205cc4248c7c6b42d03464f27d4fb74` |
| thingsboard-dependencies | 563 | 402,981,814 | `afc84c4f2d1d14fc958561d79a52de8d161e34160cfac1ee805ce57551287792` |
| thingsboard-checkout-sources-full | 123,027 | 10,437,771,541 | `8f9b06568ae1d6728696a98883f06d0f30d1d52e9a306e0dfcac74563985a2c1` |
| thingsboard-model-sources-full | 123,027 | 10,437,771,541 | `8f9b06568ae1d6728696a98883f06d0f30d1d52e9a306e0dfcac74563985a2c1` |
| thingsboard-toolchain | 306 | 271,827,620 | `c577fccfec2a6a83c4676c2ad2aa5031331138a5b5b8d1319a0246cbf5fa2024` |
| Stirling-PDF-class-roots-full | 1,890 | 10,710,712 | `81ce8fe152509ac8d9549db7d3ff77105e6bc2f12769d4c78fc9544f4e06fca2` |
| Stirling-PDF-dependencies | 364 | 180,135,898 | `8a62c5f940557c079f751b3182e6e18968071a6fc4aada3c5d9d010f9ea733b6` |
| Stirling-PDF-checkout-sources-full | 4,455 | 312,253,027 | `22563eadcfc79a717f9e666a2232c563746258d211a4e80d608f4da37e5c5603` |
| Stirling-PDF-model-sources-full | 4,456 | 312,261,713 | `acd593a710522f6afbd6985dfec75b51e70883320380e85e11e7a757e6b43daf` |
| Stirling-PDF-toolchain | 454 | 384,610,193 | `57275a904796f3525c13130a335ab20a80108b63dd06c408554aa319afe12562` |
| current-builtin-rules | 66 | 357,076 | `edb7ae89fa9ce2192054f714e933ba986317a6606e8923b3626944fe3a52dcb1` |
| conductor-passthrough | 35 | 66,582 | `6ccef26f9f3bb8e32d3ace47fcc98c2fb9b6768a8042faae103313b575dcd704` |
| conductor-dataflow-src | 48 | 76,699 | `303435acc3f5ee09b02d2229eff2cd0215e546d99d2ad1253ec24704d8a136a5` |
| conductor-rules | 5 | 8,737 | `28fbf2b85ecf2dfe69a44afbea57a9e335de02568b7ff051aedf3702f2d66eb6` |
| conductor-dataflow-compiled | 54 | 69,283 | `82952196eabfdd47895c51fd4981ba9951940182edb9d1e65c4b2cbfe0119c1b` |

Byte totals include repeated and shared source roots. They do not measure
unique physical storage. Equality holds at the audit endpoint. Recheck the
selected inputs before and after the future campaign.

| Model | SHA-256, equal to the fixed baseline |
|---|---|
| OWASP-model | `e8fd467e410051c3b0b36d461d953780e5819345fd3b7fddc68a3f8769e09873` |
| conductor-model | `3457cf5a1b3c63e0710dfa50a9fbca1c4229f2726ea3276cc409e019515ee35d` |
| thingsboard-model | `1246cb43621245e0ef971a51052b54a56abd60725860f44824f00f34d57b58f3` |
| Stirling-PDF-model | `b62263d3134af8b0c93426dedcd15a976808e4c8e838950c1a4959022d5d3ef4` |

The campaign command is prepared but has not started. It selects only
OWASP, conductor, Thingsboard and Stirling-PDF. It uses FULL run-1 marks,
statics and the default alias setting. It uses Gradle `runProjectAnalyzer`
through the existing benchmark helper.

| Project | Heap | IFDS timeout | Outer timeout |
|---|---:|---:|---:|
| OWASP | 8g | 1,000 s | 1,200 s |
| conductor | 8g | 1,080 s | 1,200 s |
| Thingsboard | 12g | 1,080 s | 1,200 s |
| Stirling-PDF | 8g | 1,080 s | 1,200 s |

The implementation must be fixed, checked and committed before these
measurements. The prepared command has no automatic launch. Its selected
runtime commit remains unset. New project scans: **0**. No new project
iteration has been reached or completed.

The detailed candidate repairs are in
[the open-contract proposal](../design/bidirectional-restricted-demand-open-contracts-20261027.md).
They remain pending user decisions. Their local formal proofs do not
select their behavior or establish whole-analyzer soundness.
