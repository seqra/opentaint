#!/usr/bin/env python3
"""Check local loop-design models; a passing kernel check does not close design decisions."""
from __future__ import annotations

import datetime
import hashlib
import importlib.util
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
MODULES = ["Control", "Geometry", "Admission", "Guidance", "Shape",
           "Protocol", "Restriction", "Feedback", "Blocks", "Decomposition", "Usefulness"]
ALLOWED_AXIOMS = {"propext", "Quot.sound"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pinned_cpu() -> None:
    if hasattr(os, "sched_getaffinity") and hasattr(os, "sched_setaffinity"):
        os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})


def main() -> None:
    # Reuse only the existing source scanner. It does not execute its main().
    scanner_path = ROOT / "spec/lean/proposals/call-stage-result-merging-analysis-20261101/check.py"
    module_spec = importlib.util.spec_from_file_location("loop_proof_source_scanner", scanner_path)
    scanner = importlib.util.module_from_spec(module_spec)
    assert module_spec.loader is not None
    module_spec.loader.exec_module(scanner)

    sources = [HERE / f"{name}.lean" for name in MODULES]
    spec_path = ROOT / "spec/loop-fragments-and-demand-collapse.md"
    inputs = sources + [HERE / "README.md", HERE / "check.py", HERE / "controls.md",
                        HERE / "controls/LoopGrowingDemandControlTest.kt",
                        HERE / "controls/control.init.gradle", scanner_path,
                        spec_path, ROOT / "spec/method-owned-loop-blocks.md",
                        ROOT / "spec/loop-fragments-and-demand-collapse-proofs.md",
                        ROOT / "spec/proof-guide.md", ROOT / "spec/lean/lean-toolchain"]
    if (ROOT / "spec/lean/lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise RuntimeError("Pinned Lean toolchain changed")
    before = {str(path.relative_to(ROOT)): sha(path) for path in inputs}
    declarations, theorem_count = [], 0
    for path in sources:
        clean = scanner.uncomment(path.read_text())
        if re.search(r"\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b", clean):
            raise RuntimeError("Unchecked or classical declaration in " + str(path))
        imports = re.findall(r"^import\s+(\S+)", clean, re.M)
        if any(name not in MODULES + ["Init", "Std"] for name in imports):
            raise RuntimeError("Unexpected import in " + str(path))
        names, count = scanner.declarations(path.read_text())
        declarations.extend(names)
        theorem_count += count

    lean = shutil.which("lean")
    if lean is None:
        raise RuntimeError("Lean is absent")
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version = subprocess.check_output([lean, "--version"], cwd=HERE, env=env, text=True).strip()
    if not re.search(r"\bversion 4\.33\.1\b", version):
        raise RuntimeError(version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    work = ROOT / "spec/lean/.lake/verification/loop-fragments-and-demand-collapse-20261102" / stamp
    work.mkdir(parents=True)
    env["LEAN_PATH"] = str(work)
    runs = []

    def run(command: list[str], log_name: str, cwd: Path) -> str:
        started = time.monotonic()
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                timeout=180, preexec_fn=pinned_cpu)
        log = work / log_name
        log.write_text(result.stdout)
        runs.append({"command": command, "cwd": str(cwd.relative_to(ROOT)),
                     "exitCode": result.returncode, "wallSeconds": time.monotonic() - started,
                     "log": str(log.relative_to(ROOT)), "logSha256": sha(log)})
        if result.returncode or re.search(r"\b(?:warning|error):", result.stdout):
            raise RuntimeError(result.stdout[-6000:])
        return result.stdout

    for name, source in zip(MODULES, sources):
        memory = "2048" if name == "Admission" else "768"
        run([lean, "-j", "1", "-M", memory, "-o", str(work / f"{name}.olean"), str(source)],
            name + ".log", HERE)
    audit = work / "Audit.lean"
    audit.write_text("\n".join(["import " + name for name in MODULES] +
                               ["#print axioms " + name for name in declarations]) + "\n")
    output = run([lean, "-j", "1", "-M", "2048", str(audit)], "Audit.log", work)
    audited = set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", output))
    axioms = set()
    for group in re.findall(r"depends on axioms: \[([^\]]*)\]", output):
        axioms.update(part.strip() for part in group.split(",") if part.strip())
    checks = {
        "allModulesAndAuditPass": True,
        "allExplicitPublicDefinitionsAndTheoremsAudited": audited == set(declarations),
        "onlyAllowedAxioms": axioms <= ALLOWED_AXIOMS,
        "noChoiceOrUnprovedAxioms": not ({"Classical.choice", "sorryAx"} & axioms),
        "inputsStable": before == {str(path.relative_to(ROOT)): sha(path) for path in inputs},
    }
    passed = all(checks.values())
    draft = "Status: draft" in spec_path.read_text()
    receipt = {
        "status": "LOCAL_MODELS_PASS" if passed else "FAILED",
        "specificationStatus": "DRAFT_DECISIONS_PENDING" if draft else "SEE_SPECIFICATION_SCOPE",
        "runtimeChanged": False,
        "runtimeVerifiedByKernel": False,
        "MethodOwnedBlockLayoutBuilderVerified": False,
        "APThreeConsumerAndProjectionAdapterVerified": False,
        "NORMALRouteRuntimeServiceSelected": False,
        "generalCrossRunConvergenceProved": False,
        "projectSpeedupMeasured": False,
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "toolchain": TOOLCHAIN, "leanVersion": version,
        "moduleCount": len(MODULES), "theoremCount": theorem_count,
        "auditedDeclarationCount": len(declarations), "declarations": declarations,
        "axiomDependencies": sorted(axioms), "checks": checks,
        "inputHashes": before, "runs": runs,
        "limits": [
            "Control and Blocks assume a supplied finite valid partition/layout, not a Kotlin decomposition pass.",
            "Geometry is scalar FULL EXACT/MAY with counted paths and a protection bit.",
            "C2 adapter certificates cover stated finite binary-path cells, not arbitrary Kotlin AP payloads.",
            "Usefulness is a reference investigation only; no NORMAL reachability service is selected.",
            "The AP composition-to-projection adapter and whole-driver refinement must still be closed.",
            "Feedback proves an exact-path counterexample to the AL/B-end-only gate, not an outlined runtime regression.",
        ],
    }
    (HERE / "checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in ["status", "specificationStatus", "theoremCount",
                                                  "auditedDeclarationCount", "axiomDependencies", "checks"]}, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
