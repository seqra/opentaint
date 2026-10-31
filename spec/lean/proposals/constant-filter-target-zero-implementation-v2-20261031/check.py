#!/usr/bin/env python3
"""Check proposal kernels. This does not verify a Kotlin implementation."""
from __future__ import annotations

import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / "spec/lean/lean-toolchain").is_file())
TOOLCHAIN = "leanprover/lean4:v4.33.1"
MODULES = ["SelectedCore", "ConstantBoundary", "TargetZeroRegistry", "InitialEmissionExact",
           "UnansweredDemand", "TargetZeroND", "SelectedTargetApplication", "TargetJoin",
           "OwnedDelta", "TerminalProtocol", "ZeroSettlement", "ProducerDomain",
           "FullZeroSourceReplay", "FullComputedLayer", "SourceSummaryCompletion", "StaticTargetClosure"]
ALLOWED_AXIOMS = {"propext", "Quot.sound"}
SPEC = ROOT / "docs/design/bidirectional-constant-filter-target-zero-implementation-20261031.md"
SPEC_SHA256 = "43fce6a3ff0adaac7361124dbe531ce2933e19437b743b22faf6d6c9b24a8a50"
PROPOSAL = ROOT / "docs/design/bidirectional-constant-filter-target-zero-implementation-v2-20261031.md"
AMENDMENT = ROOT / "spec/demand-layer-exact-initials.md"
AMENDMENT_PROOFS = ROOT / "spec/demand-layer-exact-initials-proofs.md"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def uncomment(source: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise RuntimeError("Unclosed Lean comment")
    return "".join(out)


def declarations(source: str) -> tuple[list[str], int]:
    stack, found, count = [], [], 0
    for line in uncomment(source).splitlines():
        begin = re.match(r"^\s*(namespace|section)\s*([\w.]*)", line)
        if begin:
            stack.append(begin.group(2) if begin.group(1) == "namespace" else "")
            continue
        if re.match(r"^\s*end(?:\s|$)", line):
            if not stack:
                raise RuntimeError("Unexpected end: " + line)
            stack.pop()
            continue
        match = re.match(r"^\s*(?:(?:private|protected)\s+)*(theorem|def|abbrev)\s+([\w.]+)", line)
        if match and not re.match(r"^\s*private\b", line):
            prefix = ".".join(x for x in stack if x)
            found.append((prefix + "." if prefix else "") + match.group(2))
            count += match.group(1) == "theorem"
    if stack:
        raise RuntimeError("Unclosed namespace or section")
    return found, count


def limited_child() -> None:
    if hasattr(os, "sched_getaffinity") and hasattr(os, "sched_setaffinity"):
        os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})


def main() -> None:
    if (ROOT / "spec/lean/lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise RuntimeError("Pinned toolchain changed")
    if sha(SPEC) != SPEC_SHA256:
        raise RuntimeError("Specification changed; review and update the explicit pin")
    lean = shutil.which("lean")
    if lean is None:
        raise RuntimeError("lean is absent")
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version = subprocess.check_output([lean, "--version"], cwd=HERE, env=env, text=True).strip()
    if not re.search(r"\bversion 4\.33\.1\b", version):
        raise RuntimeError(version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    work = ROOT / "spec/lean/.lake/verification/constant-filter-target-zero-implementation-v2-20261031" / stamp
    work.mkdir(parents=True)
    env["LEAN_PATH"] = str(work)
    source_paths = [HERE / (m + ".lean") for m in MODULES]
    runtime = ROOT / "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi"
    runtime_paths = [runtime / name for name in [
        "ap/RestrictedInitialPolicy.kt", "ap/RuntimeDataDomain.kt", "ap/Demand.kt", "ap/Reference.kt", "ap/Summary.kt",
        "ap/ApManager.kt", "ap/ApOps.kt", "ap/ApOut.kt", "ap/Clean.kt",
        "interp/FormApplier.kt", "interp/MicroEdge.kt", "interp/MicroEdgeBuilder.kt",
        "engine/RunMethodAnalyzer.kt", "engine/RunMethodLocalServices.kt", "engine/RunMethodCallServices.kt", "engine/MethodServices.kt",
        "engine/EngineAlgebra.kt", "engine/Run1PointResume.kt", "engine/SummaryStorage.kt",
        "engine/Target.kt", "engine/NormalTargetStore.kt", "engine/ReportCatalog.kt", "engine/RunConfig.kt",
        "engine/RunEvent.kt", "engine/RunStatus.kt", "engine/SharedObjects.kt",
        "engine/PublicationIndex.kt", "engine/CalleeSubscriptions.kt", "engine/SubscriptionManager.kt",
        "engine/UnitRunner.kt", "engine/RunMethodHandlers.kt", "engine/RunManager.kt",
        "engine/PersistedSummaryReplay.kt", "engine/JoinedStaticGuidance.kt", "store/RecordStore.kt", "store/DemandStore.kt",
        "store/StaticGuidance.kt", "store/StaticEntryLookup.kt", "store/StaticPairLookup.kt",
        "store/C5StaticDemandView.kt", "store/StaticSelectorIndex.kt",
        "store/ConjunctionStore.kt", "store/KaryJoin.kt", "store/SourceHitStore.kt", "store/ControlDemand.kt", "store/SinkEdge.kt",
        "driver/HandOff.kt", "driver/Seeds.kt", "driver/IterationDriver.kt", "driver/Report.kt",
    ]]
    runtime_paths.append(ROOT / "core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/JIRBidiAnalysis.kt")
    tests = ROOT / "core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi"
    test_paths = [tests / name for name in [
        "ExactDemandMaySourcePermissionTest.kt", "TargetCallTest.kt", "TargetProtocolTest.kt",
        "BarrierFailureTest.kt", "ReturnFullCleanupEngineTest.kt", "ReturnFullCleanupTest.kt", "Run1MarkModeTest.kt",
        "Run1FullLayerPolicyTest.kt", "BackwardSourceSummaryTargetTest.kt", "CallSourceHitTest.kt",
        "FullConditionalSourceDemandTest.kt", "StaticTargetRefinementTraceTest.kt",
        "StaticTargetClosureTest.kt", "ControlDemandTest.kt", "VirtualZeroExitTargetTest.kt",
        "Run1StaticExitRoutingTest.kt", "StaticCatalogIterationTest.kt", "StaticCatalogClosureTest.kt",
        "fixtures/StaticCatalogAssertions.kt",
    ]]
    input_paths = source_paths + [Path(__file__).resolve(), SPEC, PROPOSAL, AMENDMENT, AMENDMENT_PROOFS, HERE / "README.md"] + runtime_paths + test_paths
    before = {str(p.relative_to(ROOT)): sha(p) for p in input_paths}
    expected, theorem_count = [], 0
    for path in source_paths:
        code = uncomment(path.read_text())
        if re.search(r"\b(?:sorry|noncomputable|unsafe|partial)\b|^\s*axiom\b", code, re.M):
            raise RuntimeError("Unproved or noncomputable source: " + str(path))
        for imported in re.findall(r"^import\s+([\w.]+)\s*$", code, re.M):
            if imported not in MODULES + ["Init"]:
                raise RuntimeError("Unexpected external proof import: " + imported)
        names, count = declarations(path.read_text())
        expected.extend(names)
        theorem_count += count
    runs = []

    def run(command: list[str], name: str, directory: Path = work) -> str:
        start = time.monotonic()
        result = subprocess.run(command, cwd=directory, env=env, text=True, capture_output=True,
                                timeout=90, preexec_fn=limited_child)
        output = result.stdout + result.stderr
        log = work / name
        log.write_text(output)
        runs.append({"command": command, "exitCode": result.returncode,
                     "wallSeconds": time.monotonic() - start, "cwd": str(directory.relative_to(ROOT)),
                     "log": str(log.relative_to(ROOT)), "logSha256": sha(log)})
        if result.returncode or re.search(r"\b(?:warning|error):", output):
            raise RuntimeError(output[-6000:])
        return output

    for module, source in zip(MODULES, source_paths):
        run([lean, "-j", "1", "-M", "768", "-o", str(work / (module + ".olean")), str(source)],
            module + ".log", HERE)
    audit = work / "Audit.lean"
    audit.write_text("\n".join(["import " + m for m in MODULES] +
                               ["#print axioms " + n for n in expected]) + "\n")
    output = run([lean, "-j", "1", "-M", "768", str(audit)], "Audit.log")
    actual = set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", output))
    axioms = set()
    for group in re.findall(r"depends on axioms: \[([^\]]*)\]", output):
        axioms.update(x.strip() for x in group.split(",") if x.strip())
    checks = {
        "allCommandsPass": all(r["exitCode"] == 0 for r in runs),
        "allPublicTheoremsAndDefinitionsAudited": actual == set(expected),
        "onlyAllowedKernelAxioms": axioms <= ALLOWED_AXIOMS,
        "noChoiceOrSorry": not ({"Classical.choice", "sorryAx"} & axioms),
        "noUnprovedOrNoncomputableSource": True,
        "onlyLocalSelectedModelsImported": True,
        "specificationMatchesPin": sha(SPEC) == SPEC_SHA256,
        "inputsStableDuringCheck": before == {str(p.relative_to(ROOT)): sha(p) for p in input_paths},
    }
    receipt = {
        "status": "PASS" if all(checks.values()) else "FAILED",
        "runtimeVerifiedByThisChecker": False,
        "kernelScope": "RETAINED_PROTOCOL_PLUS_HISTORICAL_ADMISSION",
        "currentProposalConformance": "NOT_VERIFIED_BY_THIS_PACKAGE",
        "historicalSlices": [
            "InitialEmissionExact concrete MAY rejection; UnansweredDemand old-exact-emitter controls.",
            "FullZeroSourceReplay.admitExact and MAY-empty-current-gate comparisons.",
            "SourceSummaryCompletion call/no-native controls composed with the old exact emitter.",
            "FullComputedLayer.NORMAL weakened-ND-arm reporting is a pre-repair counterexample.",
        ],
        "kernelSelectedLaws": "PASS" if all(checks.values()) else "FAILED",
        "composedRuntimeCoverage": "NOT_ESTABLISHED",
        "openCoverage": [
            "Complete FULL conditional-source/caller-context behavior and known GROUP source-admission issues remain runtime obligations.",
            "The concrete amendment selects an ND repair; the pre-amendment runtime regression is not repaired by this kernel package.",
            "Static Target closure is modeled with paired C5; actual geometry/visibility/index adapters require runtime validation.",
            "Whole-project findings, convergence and performance have not been established by this kernel check.",
        ],
        "specificationSha256": SPEC_SHA256,
        "baseRuntime": "e090118e5f9603f1973c0578a3e04998035f4508",
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "toolchain": TOOLCHAIN, "leanVersion": version,
        "inputHashes": before, "theoremCount": theorem_count,
        "auditedDeclarationCount": len(expected), "auditedDeclarations": expected,
        "axiomDependencies": sorted(axioms), "checks": checks, "runs": runs,
        "scope": "Retained protocol kernels with labeled historical concrete C2 rejection, old exact-emitter call/no-native comparisons, and ZERO-only layer history. Generic truly-empty admission remains a no-op; matching concrete MAY is admitted in D by the separate amendment. This package does not verify the amended whole implementation proposal. Constant-free boundaries and conditional route preservation, exact report registry and root extraction, paired C5/handoff, selected NORMAL-only forward terminal application, arbitrary-arity complete Target joins, owned retained/seen delta equivalence, durable required publication/receipt, constructive rooted ZERO settlement and completed snapshots. The explicit amendments add ordinary FULL computed-layer preservation under ZERO and nonzero origins without promoting DEMAND; independent static/GROUP overrides; exact NORMAL source native replay before current demand, all-EXACT empty-E ZERO cleanup equivalence, and accepted backward source-summary ZERO-to-DemandTarget dispatch with preserved original and no fake source hit. The typed static Target extension proves eager/factored W/B/R closure equivalence, endpoint provenance, direct/inherited Target guides, paired ZERO C2/C5, Target/ZERO read-only exit-probe equivalence for every complete row, and finite full/group mark labels. Residual controls retain the pre-completion static paired-C5 rejection and the computed-DEMAND no-native exact/MAY admission cell and conditional NORMAL weakened-ND-arm reporting counterexample; they do not establish composed coverage. AP/JVM geometry, actual static/input binding, Kotlin synchronization/cancellation/fairness, whole-project findings, convergence and performance remain runtime/test obligations. The old concrete-MAY rejection and NORMAL weakened-ND-arm controls are historical, superseded by the new concrete exact-DEMAND package. The old ZERO-only override remains a historical comparison; its nonzero demotion is not a selected current law. No superseded source-permission workaround is imported.",
    }
    (HERE / "checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: receipt[k] for k in ["status", "theoremCount", "auditedDeclarationCount", "axiomDependencies", "checks"]}, indent=2))
    if not all(checks.values()):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
