#!/usr/bin/env python3
"""Check the pinned specification and implementation-seam models."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-directory", type=Path)
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    root = package.parents[3]
    base = package.parent / "main-migration-20261109"
    manifest = json.loads((package / "manifest.json").read_text())
    for relative, expected in manifest["files"].items():
        if digest(root / relative) != expected:
            raise SystemExit(f"Source pin mismatch: {relative}")
    base_manifest = json.loads((base / "manifest.json").read_text())
    for relative, expected in base_manifest["files"].items():
        if digest(root / relative) != expected:
            raise SystemExit(f"Specification source pin mismatch: {relative}")
    for path in (base / "MainMigration.lean", package / "Plan.lean", package / "AxiomAudit.lean"):
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|unsafe|noncomputable)\b", path.read_text(), re.M):
            raise SystemExit(f"Forbidden proof construct: {path.name}")
    output = (args.output_directory or Path(tempfile.mkdtemp(prefix="migration-impl-proof-"))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / "receipt.json").exists():
        raise SystemExit("Use a fresh output directory")
    version = subprocess.check_output(["lean", "--version"], cwd=package, text=True).strip()
    if manifest["lean_version"] not in version:
        raise SystemExit(f"Incorrect Lean version: {version}")
    env = dict(os.environ)
    env["LEAN_PATH"] = str(output) + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    steps = [
        (base, ["lean", "-o", str(output / "MainMigration.olean"), "MainMigration.lean"]),
        (package, ["lean", "-o", str(output / "Plan.olean"), "Plan.lean"]),
        (package, ["lean", "AxiomAudit.lean"]),
    ]
    logs = []
    for index, (cwd, command) in enumerate(steps):
        result = subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)
        log = result.stdout + result.stderr
        (output / f"{index + 1}.log").write_text(log)
        logs.append(log)
        if result.returncode:
            raise SystemExit(log)
    names = re.findall(r"MIGRATION_IMPL_THEOREM ([\w.]+)", logs[-1])
    final = re.search(r"MIGRATION_IMPL_AUDIT base=(\d+) plan=(\d+) examples=(\d+)", logs[-1])
    if final is None or len(set(names)) != 70:
        raise SystemExit("Incomplete theorem audit")
    counts = tuple(map(int, final.groups()))
    if counts != (51, 19, 14):
        raise SystemExit(f"Incorrect theorem counts: {counts}")
    receipt = {
        "status": "PASS",
        "lean_version": version,
        "proposal_revision": manifest["proposal_revision"],
        "main_revision": manifest["main_revision"],
        "manifest_sha256": digest(package / "manifest.json"),
        "files": manifest["files"],
        "theorems": sorted(names),
        "specification_theorem_count": 51,
        "implementation_theorem_count": 19,
        "theorem_count": 70,
        "named_finite_example_count": 14,
        "allowed_standard_axioms": ["propext", "Quot.sound"],
        "custom_axioms": False,
        "classical_choice": False,
        "proof_holes": False,
        "native_analyzer_proved": False,
        "whole_program_convergence_proved": False,
        "latest_reached_iteration": None,
        "commands": [command for _, command in steps],
    }
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("PASS: 51 specification + 19 implementation-seam theorems; "
          "14 named finite examples; no forbidden dependencies")
    print(f"Receipt: {output / 'receipt.json'}")


if __name__ == "__main__":
    main()
