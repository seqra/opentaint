#!/usr/bin/env python3
"""Check the comparative counterexample and the guarded service proof."""

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
    assert parent["status"] == "PASS" and parent["auditedDeclarations"] == 7501
    assert len(models) == 449

    # The condensed proof directory has only its new module. Its checked
    # parent directory contains the earlier compiled proof chain.
    sources = [parent_path.parent]
    earlier_path = Path(parent["parentReceipt"])
    assert digest(earlier_path) == parent["parentReceiptSha256"]
    sources.append(earlier_path.parent)
    for name, model in models.items():
        assert digest(Path(model["source"])) == model["sha256"], name
        assert any((directory / f"{name}.olean").is_file() for directory in sources), name

    out = args.out.resolve()
    assert out not in sources
    out.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "ELAN_TOOLCHAIN": "leanprover/lean4:v4.35.0",
           "LEAN_PATH": os.pathsep.join(map(str, [out, *sources]))}
    count = 0
    for module in ["CoveredOrigin", "ServiceSimulation", "NativeAdmissionCells"]:
        source = Path(__file__).resolve().with_name(f"{module}.lean")
        text = source.read_text()
        assert not re.search(r"^\s*(axiom|constant|classical)\b|\b(sorry|admit|native_decide)\b", text, re.M)
        claims = re.findall(r"^theorem (\w+)", text, re.M)
        shutil.copyfile(source, out / source.name)

        def lean(log, *arguments):
            result = subprocess.run(["lean", *arguments], cwd=out, env=env,
                                    text=True, capture_output=True)
            output = result.stdout + result.stderr
            (out / log).write_text(output)
            assert result.returncode == 0 and "warning:" not in output, output
            return output

        lean(f"{module}.log", "-o", f"{module}.olean", source.name)
        audit = out / f"{module}Audit.lean"
        audit.write_text(f"import {module}\n" + "".join(f"#print axioms {module}.{claim}\n" for claim in claims))
        report = lean(f"{module}.axioms.log", audit.name)
        audited = re.findall(
            r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", report)
        assert len(audited) == len(claims), report
        for name, axioms in audited:
            assert set(re.findall(r"[\w.]+", axioms)) <= {"propext", "Quot.sound"}, (name, axioms)
        models[module] = dict(source=str(source), sha256=digest(source), auditedDeclarations=len(claims))
        count += len(claims)
    receipt = dict(status="PASS", models=models, newDeclarations=count, parentReceipt=str(parent_path),
                   parentReceiptSha256=digest(parent_path),
                   auditedDeclarations=sum(model["auditedDeclarations"] for model in models.values()),
                   wholeNativeActivationProved=False)
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"PASS: {count} new claims, {receipt['auditedDeclarations']} cumulative, {len(models)} modules")


if __name__ == "__main__":
    main()
