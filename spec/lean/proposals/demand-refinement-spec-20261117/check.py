#!/usr/bin/env python3
"""Audit the condensed contract against the pinned constructive proof chain."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dependencies", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    parent_path = (args.dependencies / "receipt.json").resolve()
    parent = json.loads(parent_path.read_text())
    models = dict(parent["models"])
    assert parent["status"] == "PASS" and parent["auditedDeclarations"] == 7494
    assert len(models) == 448
    for name, model in models.items():
        assert digest(Path(model["source"])) == model["sha256"], name
        assert (parent_path.parent / f"{name}.olean").is_file(), name

    module = "CondensedDemandRefinement"
    source = Path(__file__).resolve().with_name(f"{module}.lean")
    text = source.read_text()
    assert not re.search(r"^\s*(axiom|constant|classical)\b|\b(sorry|admit|native_decide)\b", text, re.M)
    claims = re.findall(r"^theorem (\w+)", text, re.M)
    out = args.out.resolve()
    assert out != parent_path.parent
    out.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, out / source.name)
    env = {**os.environ, "ELAN_TOOLCHAIN": "leanprover/lean4:v4.35.0",
           "LEAN_PATH": os.pathsep.join(map(str, (out, parent_path.parent)))}

    def lean(log, *arguments):
        result = subprocess.run(["lean", *arguments], cwd=out, env=env,
                                text=True, capture_output=True)
        output = result.stdout + result.stderr
        (out / log).write_text(output)
        assert result.returncode == 0 and "warning:" not in output, output
        return output

    lean("compile.log", "-o", f"{module}.olean", source.name)
    audit = out / "Audit.lean"
    audit.write_text(f"import {module}\n" + "".join(f"#print axioms {module}.{claim}\n" for claim in claims))
    report = lean("axioms.log", audit.name)
    audited = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", report)
    assert len(audited) == len(claims), report
    for name, axioms in audited:
        assert set(re.findall(r"[\w.]+", axioms)) <= {"propext", "Quot.sound"}, (name, axioms)
    models[module] = dict(source=str(source), sha256=digest(source), auditedDeclarations=len(audited))
    receipt = dict(status="PASS", models=models, newDeclarations=len(audited),
                   parentReceipt=str(parent_path), parentReceiptSha256=digest(parent_path),
                   auditedDeclarations=sum(model["auditedDeclarations"] for model in models.values()),
                   wholeAnalyzerNoFalseNegativeProof=False, wholeAnalyzerTerminationProof=False)
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"PASS: {len(audited)} new claims, {receipt['auditedDeclarations']} cumulative, {len(models)} modules")


if __name__ == "__main__":
    main()
