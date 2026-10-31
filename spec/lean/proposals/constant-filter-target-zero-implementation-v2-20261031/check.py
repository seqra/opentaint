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
           "OwnedDelta", "TerminalProtocol", "ZeroSettlement", "ProducerDomain"]
ALLOWED_AXIOMS = {"propext", "Quot.sound"}
SPEC = ROOT / "docs/design/bidirectional-constant-filter-target-zero-implementation-20261031.md"
SPEC_SHA256 = "8ae901c30188e81a09030491291dbb86a749e017a6d0b4b3218664821494c21a"
PROPOSAL = ROOT / "docs/design/bidirectional-constant-filter-target-zero-implementation-v2-20261031.md"


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
        "ap/RestrictedInitialPolicy.kt", "ap/Demand.kt", "ap/Reference.kt", "ap/Summary.kt",
        "interp/FormApplier.kt", "interp/MicroEdge.kt", "interp/MicroEdgeBuilder.kt",
        "engine/RunMethodAnalyzer.kt", "engine/RunMethodLocalServices.kt", "engine/RunMethodCallServices.kt", "engine/MethodServices.kt",
        "engine/EngineAlgebra.kt", "engine/Run1PointResume.kt", "engine/SummaryStorage.kt",
        "engine/PublicationIndex.kt", "engine/CalleeSubscriptions.kt", "engine/SubscriptionManager.kt",
        "engine/UnitRunner.kt", "engine/RunMethodHandlers.kt", "engine/RunManager.kt",
        "engine/PersistedSummaryReplay.kt", "store/RecordStore.kt", "store/DemandStore.kt",
        "store/ConjunctionStore.kt", "store/KaryJoin.kt", "store/SourceHitStore.kt",
        "driver/HandOff.kt", "driver/Seeds.kt", "driver/IterationDriver.kt", "driver/Report.kt",
    ]]
    runtime_paths.append(ROOT / "core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/JIRBidiAnalysis.kt")
    input_paths = source_paths + [Path(__file__).resolve(), SPEC, PROPOSAL, HERE / "README.md"] + runtime_paths
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
        "proposalReadyForImplementation": True,
        "openDecision": None,
        "specificationSha256": SPEC_SHA256,
        "baseRuntime": "e090118e5f9603f1973c0578a3e04998035f4508",
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "toolchain": TOOLCHAIN, "leanVersion": version,
        "inputHashes": before, "theoremCount": theorem_count,
        "auditedDeclarationCount": len(expected), "auditedDeclarations": expected,
        "axiomDependencies": sorted(axioms), "checks": checks, "runs": runs,
        "scope": "Clean v2 selected protocol models only. Directed C2, no-op unsatisfied admission, constant-free boundaries and conditional route preservation, exact report registry and root extraction, paired C5/handoff, selected NORMAL-only forward terminal application, arbitrary-arity complete Target joins, owned retained/seen delta equivalence, durable required publication/receipt, constructive rooted ZERO settlement and completed snapshots. AP/JVM geometry, actual static/input binding, Kotlin synchronization/cancellation/fairness, whole-project findings, convergence and performance remain runtime/test obligations. No superseded promotion or source-permission workaround is imported.",
    }
    (HERE / "checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: receipt[k] for k in ["status", "theoremCount", "auditedDeclarationCount", "axiomDependencies", "checks"]}, indent=2))
    if not all(checks.values()):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
