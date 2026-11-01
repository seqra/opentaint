#!/usr/bin/env python3
"""Check a future local design model. This does not select or verify an implementation."""
from __future__ import annotations
import argparse
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
REVIEWED_RUNTIME = "86ad3b70b5b834d60bc0fe96a91091174265c827"
MODULES = ["Keys", "Results", "Suffix", "Work"]
ALLOWED_AXIOMS = {"propext", "Quot.sound"}
DOSSIER = ROOT / "spec/call-stage-result-merging-analysis-proofs.md"


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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true",
                        help="Write a NOT_RUN source inventory without starting Lean")
    args = parser.parse_args()
    if (ROOT / "spec/lean/lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise RuntimeError("Pinned toolchain changed")
    sources = [HERE / (module + ".lean") for module in MODULES]
    runtime = ROOT / "core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi"
    context = [runtime / name for name in [
        "engine/RunMethodCallServices.kt", "engine/Run1PointResume.kt", "engine/EngineAlgebra.kt",
        "interp/CallPlan.kt", "interp/FormApplier.kt", "ap/Conclusions.kt",
    ]]
    inputs = sources + [DOSSIER, HERE / "README.md", Path(__file__).resolve(),
                        ROOT / "spec/proof-guide.md", ROOT / "spec/lean/lean-toolchain"] + context
    before = {str(path.relative_to(ROOT)): sha(path) for path in inputs}
    for path in context:
        relative = str(path.relative_to(ROOT))
        reviewed = subprocess.check_output(["git", "show", REVIEWED_RUNTIME + ":" + relative], cwd=ROOT)
        if hashlib.sha256(reviewed).hexdigest() != sha(path):
            raise RuntimeError("Reviewed runtime context changed: " + relative)
    inventory, theorem_count = [], 0
    for path in sources:
        raw = path.read_text()
        clean = uncomment(raw)
        if re.search(r"\b(?:axiom|sorry|admit|noncomputable|unsafe|partial|native_decide|Classical)\b", clean):
            raise RuntimeError("Forbidden unchecked or classical source in " + str(path))
        imports = re.findall(r"^import\s+(\S+)", clean, re.M)
        if any(module not in MODULES + ["Init", "Std"] for module in imports):
            raise RuntimeError("Unexpected import in " + str(path))
        names, count = declarations(raw)
        inventory.extend(names)
        theorem_count += count
    receipt = {
        "status": "NOT_RUN",
        "kernelChecks": "PENDING_AFTER_ACTIVE_CAMPAIGN",
        "futureCandidateSelected": False,
        "runtimeImplementationChangedByThisPackage": False,
        "runtimeVerifiedByThisChecker": False,
        "reviewedRuntimeContextCommit": REVIEWED_RUNTIME,
        "wholeAnalyzerFindingEquivalence": "NOT_ESTABLISHED",
        "statefulProducerEffectEquivalence": "REQUIRES_RUNTIME_ADAPTER_PROOFS",
        "projectPerformance": "NOT_MEASURED",
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "toolchain": TOOLCHAIN,
        "moduleCount": len(MODULES),
        "declaredTheoremCount": theorem_count,
        "kernelCheckedTheoremCount": 0,
        "declarationInventory": inventory,
        "inputHashes": before,
        "sourceInventoryChecks": {
            "onlyAllowedImports": True,
            "noUncheckedOrClassicalSource": True,
            "runtimeContextMatchesReviewedCommit": True,
        },
    }
    if args.prepare_only:
        receipt["inputsStableDuringPreparation"] = before == {
            str(path.relative_to(ROOT)): sha(path) for path in inputs}
        (HERE / "checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(json.dumps({key: receipt[key] for key in
                         ["status", "kernelChecks", "moduleCount", "declaredTheoremCount"]}, indent=2))
        return
    lean = shutil.which("lean")
    if lean is None:
        raise RuntimeError("lean is absent")
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version = subprocess.check_output([lean, "--version"], cwd=HERE, env=env, text=True).strip()
    if not re.search(r"\bversion 4\.33\.1\b", version):
        raise RuntimeError(version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    work = ROOT / "spec/lean/.lake/verification/call-stage-result-merging-analysis-20261101" / stamp
    work.mkdir(parents=True)
    env["LEAN_PATH"] = str(work)
    runs = []

    def run(command: list[str], log: str, cwd: Path = work) -> str:
        started = time.monotonic()
        result = subprocess.run(command, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=90, preexec_fn=limited_child)
        output = result.stdout
        path = work / log
        path.write_text(output)
        runs.append({"command": command, "cwd": str(cwd.relative_to(ROOT)), "exitCode": result.returncode,
                     "wallSeconds": time.monotonic() - started, "log": str(path.relative_to(ROOT)),
                     "logSha256": sha(path)})
        if result.returncode or re.search(r"\b(?:warning|error):", output):
            raise RuntimeError(output[-6000:])
        return output

    for module, source in zip(MODULES, sources):
        run([lean, "-j", "1", "-M", "768", "-o", str(work / (module + ".olean")), str(source)],
            module + ".log", source.parent)
    audit = work / "Audit.lean"
    audit.write_text("\n".join(["import " + module for module in MODULES] +
                               ["#print axioms " + name for name in inventory]) + "\n")
    output = run([lean, "-j", "1", "-M", "768", str(audit)], "Audit.log")
    actual = set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", output))
    axioms = set()
    for group in re.findall(r"depends on axioms: \[([^\]]*)\]", output):
        axioms.update(value.strip() for value in group.split(",") if value.strip())
    checks = {
        "allCommandsPass": all(row["exitCode"] == 0 for row in runs),
        "allExplicitPublicDefinitionsAndTheoremsAudited": actual == set(inventory),
        "onlyAllowedKernelAxioms": axioms <= ALLOWED_AXIOMS,
        "noChoiceOrSorry": not ({"Classical.choice", "sorryAx"} & axioms),
        "noUncheckedOrClassicalSource": True,
        "runtimeContextMatchesReviewedCommit": True,
        "inputsStableDuringCheck": before == {str(path.relative_to(ROOT)): sha(path) for path in inputs},
    }
    passed = all(checks.values())
    receipt.update({
        "status": "PASS" if passed else "FAILED",
        "kernelChecks": "PASS" if passed else "FAILED",
        "kernelCheckedTheoremCount": theorem_count if passed else 0,
        "auditedDeclarationCount": len(inventory),
        "axiomDependencies": sorted(axioms),
        "leanVersion": version,
        "checks": checks,
        "runs": runs,
        "scope": "Finite exact complete-key result merging and pointwise protection OR; ordinary/protected observation preservation; deterministic OR-preserving fixed-suffix set equivalence; executable 64-to-1 alias continuation and 65-to-2 total work witness with explicit collection-cost condition. No stateful Kotlin effect-order, global scheduling, whole-project finding or performance equivalence is established.",
    })
    (HERE / "checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in
                     ["status", "kernelCheckedTheoremCount", "auditedDeclarationCount", "axiomDependencies", "checks"]}, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
