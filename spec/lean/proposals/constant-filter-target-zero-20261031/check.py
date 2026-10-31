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
MODULES = ["TargetZeroKernel", "TargetZeroRegistry", "TargetZeroND", "ConstantBoundary",
           "TargetZeroSourcePermission", "InitialEmissionExact", "UnansweredDemand",
           "SelectedTargetApplication", "NormalTargetPersistence"]
ALLOWED_AXIOMS = {"propext", "Quot.sound"}
PROPOSAL = ROOT / "docs/design/bidirectional-constant-filter-target-zero-implementation-20261031.md"


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
    lean = shutil.which("lean")
    if lean is None:
        raise RuntimeError("lean is absent")
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version = subprocess.check_output([lean, "--version"], cwd=HERE, env=env, text=True).strip()
    if not re.search(r"\bversion 4\.33\.1\b", version):
        raise RuntimeError(version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    work = ROOT / "spec/lean/.lake/verification/constant-filter-target-zero-20261031" / stamp
    work.mkdir(parents=True)
    env["LEAN_PATH"] = str(work)
    source_paths = [HERE / (m + ".lean") for m in MODULES]
    input_paths = source_paths + [Path(__file__).resolve(), PROPOSAL, HERE / "README.md"]
    before = {str(p.relative_to(ROOT)): sha(p) for p in input_paths}
    expected, theorem_count = [], 0
    for path in source_paths:
        code = uncomment(path.read_text())
        if re.search(r"\b(?:sorry|noncomputable)\b|^\s*axiom\b", code, re.M):
            raise RuntimeError("Unproved or noncomputable source: " + str(path))
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
        "inputsStableDuringCheck": before == {str(p.relative_to(ROOT)): sha(p) for p in input_paths},
    }
    receipt = {
        "status": "PASS" if all(checks.values()) else "FAILED",
        "runtimeVerifiedByThisChecker": False,
        "proposalReadyForImplementation": True,
        "openDecision": None,
        "baseRuntime": "e090118e5f9603f1973c0578a3e04998035f4508",
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "toolchain": TOOLCHAIN, "leanVersion": version,
        "inputHashes": before, "theoremCount": theorem_count,
        "auditedDeclarationCount": len(expected), "auditedDeclarations": expected,
        "axiomDependencies": sorted(axioms), "checks": checks, "runs": runs,
        "scope": "Proposal kernels only. Constants: conditional preservation on routes with no constant intermediate. Targets: local control, paired demand, finite support routes, registry, binary complete ND/seed controls, selected all-NORMAL application, backward exclusion, exact owned-row dedup, and settled ZERO replay suppression. Exact C2 is directed; ANY cannot answer EXACT; unsatisfied admission and all-unsatisfied batches require no special action. Pre-correction promotion/source-permission examples are historical. AP geometry, production fixed-point settlement/barrier ordering, Kotlin refinement, scheduling, whole-project findings and convergence remain implementation/test obligations.",
    }
    (HERE / "checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: receipt[k] for k in ["status", "theoremCount", "auditedDeclarationCount", "axiomDependencies", "checks"]}, indent=2))
    if not all(checks.values()):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
