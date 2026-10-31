#!/usr/bin/env python3
"""Check constructive design kernels; this does not verify Kotlin."""
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
MODULES = ["Domain", "ExactAdmission", "C2C5Image", "AdmissionStore", "AdmissionBounds",
           "NDProjection", "FactoredOrigins", "ResultLanes", "TargetLayers", "Pipeline", "IntrinsicMayCycle"]
ALLOWED_AXIOMS = {"propext", "Quot.sound"}
SPEC = ROOT / "spec/demand-layer-exact-initials.md"
DOSSIER = ROOT / "spec/demand-layer-exact-initials-proofs.md"
PROPOSAL = ROOT / "docs/design/bidirectional-constant-filter-target-zero-implementation-v2-20261031.md"
SPEC_SHA256 = "a37aeee246f5373f933269f3babd20a18e71d33a0b950021f612c0545e0c58d7"

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
    work = ROOT / "spec/lean/.lake/verification/demand-layer-exact-initials-20261031" / stamp
    work.mkdir(parents=True)
    env["LEAN_PATH"] = str(work)
    sources = [HERE / (module + ".lean") for module in MODULES]
    runtime = ROOT / "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi"
    reference_paths = [runtime / name for name in [
        "ap/RestrictedInitialPolicy.kt", "ap/AdmittedInitial.kt", "ap/Demand.kt", "ap/Reference.kt",
        "engine/RunMethodAnalyzer.kt", "engine/Run1Abstraction.kt", "engine/RunMethodLocalServices.kt",
        "engine/RunMethodCallServices.kt", "engine/Target.kt", "store/InitialFacts.kt",
        "engine/RestrictedInitialEmission.kt", "engine/Run1RequestMatching.kt",
        "engine/RunEvent.kt", "engine/RunnerPort.kt", "engine/UnitRunner.kt", "engine/RunMethodHandlers.kt",
        "engine/SubscriptionManager.kt", "store/DemandResultCoverage.kt",
        "store/Run1OriginPredicateStore.kt",
        "store/Run1OriginConjunctionStore.kt", "store/RecordStore.kt", "store/DemandStore.kt",
    ]]
    inputs = sources + [SPEC, DOSSIER, PROPOSAL, HERE / "README.md", Path(__file__).resolve()] + reference_paths
    before = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    expected, theorem_count = [], 0
    for path in sources:
        raw = path.read_text()
        clean = uncomment(raw)
        if re.search(r"\b(?:axiom|sorry|admit|noncomputable|unsafe|partial)\b", clean):
            raise RuntimeError("Forbidden unchecked declaration in " + str(path))
        imports = re.findall(r"^import\s+(\S+)", clean, re.M)
        if any(module not in MODULES + ["Init"] for module in imports):
            raise RuntimeError("Only local constructive modules may be imported: " + str(path))
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
            module + ".log", HERE)
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
        "onlyLocalModelsImported": True,
        "specificationMatchesPin": sha(SPEC) == SPEC_SHA256,
        "inputsStableDuringCheck": before == {str(p.relative_to(ROOT)): sha(p) for p in inputs},
    }
    passed = all(checks.values())
    receipt = {
        "status": "PASS" if passed else "FAILED",
        "kernelSelectedLaws": "PASS" if passed else "FAILED",
        "runtimeImplementation": "NOT_ESTABLISHED_BY_KERNEL_CHECK",
        "runtimeVerifiedByThisChecker": False,
        "implementationProposalBinding": "SOURCE_ALIGNMENT_ONLY_NOT_KOTLIN_VERIFICATION",
        "composedKotlinCoverage": "NOT_ESTABLISHED",
        "FLOW": "UNCHANGED_OUTSIDE_SELECTED_CONCRETE_SCOPE",
        "generalCrossIterationTermination": "NOT_CLAIMED_INTRINSIC_MAY_COUNTEREXAMPLE",
        "specificationSha256": SPEC_SHA256,
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "toolchain": TOOLCHAIN, "leanVersion": version,
        "moduleCount": len(MODULES), "theoremCount": theorem_count,
        "auditedDeclarationCount": len(expected), "auditedDeclarations": expected,
        "inputHashes": before, "axiomDependencies": sorted(axioms), "checks": checks, "runs": runs,
        "scope": "Design-only concrete FULL exact data admission under directed paths, matching marks, empty exact-demand exclusion, actual descent exclusions and positive field budgets. Starting layer is actual uncertainty plus coercion loss, not the old guide layer. Canonical descriptors precede N/D dedup; both lanes and protection upgrades remain distinct. C5 exact-entry image has an executable C2 witness. Dependent chains preserve D, legal MAY caller support rejects cached NormalTarget, and D data has no NORMAL report/native record. Source/sink origin weakening retains complete support or yields D; factored column search is equivalent to eager Cartesian existence, with executable witnesses, binary practical cost bounds, and incremental support-classification laws: nonzero Q growth preserves other P and all-ZERO tests, while ZERO growth requires a full revisit. Existing protection/version invalidation is not removed. A finite F1/B2/F3 producer/source/sink model includes real source-action permissions and same-call ND, and proves the good report and negative controls by F3 without claiming a driver stop. Intrinsic MAY constructs a repeatable finite F/B frontier with existing native source replay and no invented source guide/hit. ZERO, static/GROUP policy, other admission cells, JVM/AP adapters, scheduling and real-project findings are not redefined or verified.",
    }
    (HERE / "checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in ["status", "moduleCount", "theoremCount", "auditedDeclarationCount", "axiomDependencies", "checks"]}, indent=2))
    if not passed:
        raise SystemExit(1)

if __name__ == "__main__":
    main()
