#!/usr/bin/env python3
"""Compile the pinned constructive model and audit every theorem dependency."""
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
    manifest = json.loads((package / "manifest.json").read_text())
    for relative, expected in manifest["files"].items():
        if digest(root / relative) != expected:
            raise SystemExit(f"Source pin mismatch: {relative}")
    for name in ("MainMigration.lean", "AxiomAudit.lean"):
        source = (package / name).read_text()
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|unsafe|noncomputable)\b", source, re.M):
            raise SystemExit(f"Forbidden proof construct in {name}")
    output = args.output_directory or Path(tempfile.mkdtemp(prefix="main-migration-proof-"))
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / "receipt.json").exists():
        raise SystemExit("Use a fresh proof output directory")
    version = subprocess.check_output(["lean", "--version"], cwd=package, text=True).strip()
    if manifest["lean_version"] not in version:
        raise SystemExit(f"Incorrect Lean version: {version}")
    env = dict(os.environ)
    env["LEAN_PATH"] = str(output) + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    logs = []
    commands = [
        ["lean", "-o", str(output / "MainMigration.olean"), "MainMigration.lean"],
        ["lean", "AxiomAudit.lean"],
    ]
    for index, command in enumerate(commands):
        result = subprocess.run(command, cwd=package, env=env, text=True, capture_output=True)
        log = result.stdout + result.stderr
        (output / f"{index + 1}.log").write_text(log)
        logs.append(log)
        if result.returncode:
            raise SystemExit(log)
    match = re.search(r"MAIN_MIGRATION_AUDIT theorems=(\d+)", logs[-1])
    if match is None:
        raise SystemExit("The axiom audit did not finish")
    names = re.findall(r"MAIN_MIGRATION_THEOREM (MainMigration\.[\w.]+)", logs[-1])
    count = int(match.group(1))
    if len(set(names)) != count:
        raise SystemExit("Incomplete theorem dependency output")
    example_count = sum(".Examples." in name for name in names)
    if count != manifest["expected_theorem_count"] or example_count != manifest["expected_example_count"]:
        raise SystemExit("The checked theorem/example inventory differs from the specification")
    receipt = {
        "status": "PASS",
        "lean_version": version,
        "base_revision": manifest["base_revision"],
        "main_revision": manifest["main_revision"],
        "manifest_sha256": digest(package / "manifest.json"),
        "files": manifest["files"],
        "theorems": sorted(names),
        "theorem_count": count,
        "finite_example_count": example_count,
        "allowed_standard_axioms": ["propext", "Quot.sound"],
        "custom_axioms": False,
        "classical_choice": False,
        "proof_holes": False,
        "native_analyzer_proved": False,
        "whole_program_convergence_proved": False,
        "latest_reached_iteration": None,
        "commands": commands,
    }
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"PASS: {count} constructive component theorems; "
          f"{receipt['finite_example_count']} finite example proofs; no forbidden dependencies")
    print(f"Receipt: {output / 'receipt.json'}")


if __name__ == "__main__":
    main()
