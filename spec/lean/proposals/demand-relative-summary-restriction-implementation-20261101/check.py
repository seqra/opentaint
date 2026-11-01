#!/usr/bin/env python3
"""Check constructive design models, not Kotlin implementation correctness."""
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
RUNTIME_COMMIT = "c4a71246519ee5432879ce82518823f1703f3aa4"
MODULES = ["Geometry", "Restriction", "Annotations", "Admission", "Controls",
           "Integration", "Progress", "SourceProgress", "AdapterPipeline", "WorkloadAccounting"]
ALLOWED_AXIOMS = {"propext", "Quot.sound"}
SPEC = ROOT / "spec/demand-relative-summary-restriction.md"
DOSSIER = ROOT / "spec/demand-relative-summary-restriction-implementation-proofs.md"
DEPENDENCIES = HERE.parent / "demand-relative-summary-restriction-20261101"
PROPOSAL = ROOT / "docs/design/bidirectional-demand-relative-summary-restriction-implementation-20261101.md"
PROPOSAL_SHA256 = "fc6a3f1adfe7dd8ed1ec90fa83bcde86b48a679eadaca476a44e143ba24e2f31"
SPEC_SHA256 = "c92fe9df643ad414c3e9397444ceb4a087e4c3417bb4670ef35909602792ba50"


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
                raise RuntimeError("Unexpected namespace end: " + line)
            stack.pop()
            continue
        match = re.match(r"^\s*(?:(?:private|protected)\s+)*(theorem|def|abbrev)\s+([\w.?]+)", line)
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
    if sha(PROPOSAL) != PROPOSAL_SHA256:
        raise RuntimeError("Implementation proposal changed; review and update the explicit pin")
    lean = shutil.which("lean")
    if lean is None:
        raise RuntimeError("lean is absent")
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version = subprocess.check_output([lean, "--version"], cwd=HERE, env=env, text=True).strip()
    if not re.search(r"\bversion 4\.33\.1\b", version):
        raise RuntimeError(version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    work = ROOT / "spec/lean/.lake/verification/demand-relative-summary-restriction-implementation-20261101" / stamp
    work.mkdir(parents=True)
    env["LEAN_PATH"] = str(work)
    sources = [(HERE if (HERE / (module + ".lean")).is_file() else DEPENDENCIES) / (module + ".lean") for module in MODULES]
    runtime = ROOT / "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi"
    reference_paths = [runtime / name for name in [
        "ap/RestrictedInitialPolicy.kt", "ap/AdmittedInitial.kt", "ap/Reference.kt", "ap/Limit.kt",
        "ap/Demand.kt", "ap/ApOps.kt", "ap/ApOut.kt", "engine/RunMethodAnalyzer.kt", "engine/RunMethodCallServices.kt",
        "engine/RunMethodLocalServices.kt", "engine/Run1Abstraction.kt", "engine/Target.kt",
        "store/RunSummaries.kt", "store/RecordStore.kt", "store/DemandStore.kt",
        "store/DemandResultCoverage.kt", "ap/FlowBackedCoverage.kt", "store/FlowBackedSummaries.kt",
        "store/MethodEdges.kt", "driver/HandOff.kt", "store/StaticPairLookup.kt",
        "engine/JoinedStaticGuidance.kt", "driver/IterationDriver.kt", "store/DiagonalRelations.kt",
        "store/RelationCensus.kt", "ap/AccessorTable.kt", "ap/PathNode.kt", "ap/LeafViews.kt",
    ]]
    inputs = sources + [SPEC, DOSSIER, PROPOSAL, DEPENDENCIES / "README.md",
                        ROOT / "spec/demand-relative-summary-restriction-proofs.md",
                        HERE / "README.md", Path(__file__).resolve()] + reference_paths
    before = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    for path in reference_paths:
        relative = str(path.relative_to(ROOT))
        reviewed = subprocess.check_output(["git", "show", RUNTIME_COMMIT + ":" + relative], cwd=ROOT)
        if hashlib.sha256(reviewed).hexdigest() != sha(path):
            raise RuntimeError("Reviewed runtime source changed: " + relative)
    expected, theorem_count = [], 0
    for path in sources:
        raw = path.read_text()
        clean = uncomment(raw)
        if re.search(r"\b(?:axiom|sorry|admit|noncomputable|unsafe|partial)\b", clean):
            raise RuntimeError("Forbidden unchecked declaration in " + str(path))
        imports = re.findall(r"^import\s+(\S+)", clean, re.M)
        if any(module not in MODULES + ["Init", "Std"] for module in imports):
            raise RuntimeError("Unexpected import: " + str(path))
        names, count = declarations(raw)
        expected.extend(names)
        theorem_count += count
    runs = []

    def run(command: list[str], log: str, cwd: Path = work) -> str:
        started = time.monotonic()
        result = subprocess.run(command, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=90, preexec_fn=limited_child)
        output = result.stdout
        log_path = work / log
        log_path.write_text(output)
        runs.append({"command": command, "cwd": str(cwd.relative_to(ROOT)), "exitCode": result.returncode,
                     "wallSeconds": time.monotonic() - started, "log": str(log_path.relative_to(ROOT)),
                     "logSha256": sha(log_path)})
        if result.returncode or re.search(r"\b(?:warning|error):", output):
            raise RuntimeError(output[-6000:])
        return output

    for module, source in zip(MODULES, sources):
        run([lean, "-j", "1", "-M", "768", "-o", str(work / (module + ".olean")), str(source)],
            module + ".log", source.parent)
    audit = work / "Audit.lean"
    audit.write_text("\n".join(["import " + module for module in MODULES] +
                               ["#print axioms " + name for name in expected]) + "\n")
    output = run([lean, "-j", "1", "-M", "768", str(audit)], "Audit.log")
    actual = set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", output))
    axioms = set()
    for group in re.findall(r"depends on axioms: \[([^\]]*)\]", output):
        axioms.update(value.strip() for value in group.split(",") if value.strip())
    checks = {
        "allCommandsPass": all(row["exitCode"] == 0 for row in runs),
        "allPublicTheoremsAndDefinitionsAudited": actual == set(expected),
        "onlyAllowedKernelAxioms": axioms <= ALLOWED_AXIOMS,
        "noChoiceOrSorry": not ({"Classical.choice", "sorryAx"} & axioms),
        "noUnprovedOrNoncomputableSource": True,
        "onlySelectedConstructiveModelsImported": True,
        "specificationMatchesPin": sha(SPEC) == SPEC_SHA256,
        "implementationProposalMatchesPin": sha(PROPOSAL) == PROPOSAL_SHA256,
        "referenceRuntimeBytesMatchReviewedCommit": True,
        "inputsStableDuringCheck": before == {str(p.relative_to(ROOT)): sha(p) for p in inputs},
    }
    passed = all(checks.values())
    receipt = {
        "status": "PASS" if passed else "FAILED",
        "kernelSelectedLaws": "PASS" if passed else "FAILED",
        "runtimeImplementation": "UNCHANGED_NOT_VERIFIED_BY_KERNEL",
        "runtimeVerifiedByThisChecker": False,
        "wholeAnalyzerFindingEquivalence": "NOT_ESTABLISHED",
        "generalCrossIterationTermination": "NOT_CLAIMED",
        "projectPerformance": "NOT_MEASURED_FOR_THIS_POLICY",
        "reviewedRuntimeCommit": RUNTIME_COMMIT,
        "specificationSha256": SPEC_SHA256,
        "implementationProposalSha256": PROPOSAL_SHA256,
        "implementationProposalStatus": "DESIGN_ONLY_NOT_IMPLEMENTED",
        "adapterTheoremCount": sum(declarations(p.read_text())[1] for p in sources if p.parent == HERE),
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "toolchain": TOOLCHAIN, "leanVersion": version,
        "moduleCount": len(MODULES), "theoremCount": theorem_count,
        "auditedDeclarationCount": len(expected), "auditedDeclarations": expected,
        "inputHashes": before, "axiomDependencies": sorted(axioms), "checks": checks, "runs": runs,
        "scope": "Implementation-adapter proofs for fixed-gate finite-leaf/delta distribution, complete-row witnesses, singleton Reach saturation and equivalent Target existential query, final header/view selection including normal ND/backward ZERO, packed-header key independence, and measurement counterexamples. Dependency scope: paired empty-E concrete FULL scalar C5 and demand-relative summary cut, counted field/array depth and uncounted static anchors; candidate-location coverage with symbolic FLOW/concrete marks and field-exclusion widening; operational admitted-only state and scalar gate/store integration; final DEMAND classification plus separate existing NORMAL ND/backward-ZERO control selector; unchanged typed Target lane; finite conditional refinement, actual-source-permission boundary witness and output compression. No raw NORMAL fallback, unselected source route, general convergence, packed Kotlin refinement or whole-project finding/performance claim.",
    }
    (HERE / "checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in ["status", "moduleCount", "theoremCount", "adapterTheoremCount",
               "auditedDeclarationCount", "axiomDependencies", "checks"]}, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
