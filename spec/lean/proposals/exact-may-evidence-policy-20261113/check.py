#!/usr/bin/env python3
"""Compile the proposal's constructive models outside the repository."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    repo = package.parents[3]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    sources = {
        "Evidence": package.parent / "truncation-evidence-20261113/Evidence.lean",
        "DualStarts": package.parent / "dual-exact-may-starts-20261113/DualStarts.lean",
        **{name: package / (name + ".lean") for name in ["Emission", "Capture", "Priority", "ViewCover", "StarAdmissionComparison"]},
    }
    audited = []
    receipt = {"leanVersion": subprocess.check_output(["lean", "--version"], text=True).strip(),
               "scope": "proposal components; not full runtime correspondence or universal convergence", "models": {}}
    for module, source in sources.items():
        target = out / (module + ".lean")
        shutil.copy2(source, target)
        text = target.read_text()
        assert not re.search(r"^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b", text, re.M), source
        command = ["lean", "-o", module + ".olean", module + ".lean"]
        run = subprocess.run(command, cwd=out, env={**os.environ, "LEAN_PATH": str(out)}, capture_output=True, text=True)
        log = run.stdout + run.stderr
        (out / (module + ".txt")).write_text(log)
        if run.returncode:
            print(log)
            raise SystemExit(run.returncode)
        assert "sorryAx" not in log and "Classical.choice" not in log, module
        declarations = []
        for line in log.splitlines():
            if "does not depend on any axioms" in line:
                declarations.append(line)
            elif "depends on axioms:" in line:
                dependencies = set(re.search(r"\[(.*)\]", line)[1].split(", "))
                assert dependencies <= {"propext", "Quot.sound"}, (module, line)
                declarations.append(line)
        assert declarations, module
        audited.extend(declarations)
        receipt["models"][module] = {"source": str(source.relative_to(repo)), "sourceSha256": sha(source),
                                    "objectSha256": sha(out / (module + ".olean")), "audited": len(declarations)}
    receipt["auditedDeclarations"] = len(audited)
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "models": len(sources), "auditedDeclarations": len(audited),
                      "receipt": str(out / "receipt.json")}, indent=2))


if __name__ == "__main__":
    main()
