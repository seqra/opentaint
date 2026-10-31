#!/usr/bin/env python3
"""Run small controls against existing AP classes; do not run Gradle/analyzer."""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import shlex
import subprocess


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    here = Path(__file__).resolve().parent
    root = next(p for p in here.parents if (p / "spec/lean/lean-toolchain").is_file())
    parser = argparse.ArgumentParser()
    parser.add_argument("--compiler-options", type=Path, required=True,
                        help="Existing Kotlin compiler options file which contains -classpath")
    args = parser.parse_args()
    options = args.compiler_options.resolve()
    module = root / "core/opentaint-dataflow-core/opentaint-dataflow"
    compiler_args = shlex.split(options.read_text())
    dependency_cp = compiler_args[compiler_args.index("-classpath") + 1]
    cp = ":".join([str(module / "build/classes/java/main"),
                   str(module / "build/classes/kotlin/main"),
                   str(module / "build/classes/kotlin/test"), dependency_cp])
    missing = [x for x in cp.split(":") if not Path(x).exists()]
    if missing:
        raise RuntimeError("Missing existing classpath inputs: " + repr(missing))
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    work = root / "spec/lean/.lake/verification/constant-filter-target-zero-20261031" / ("ap-" + stamp)
    work.mkdir(parents=True)
    classes = work / "classes"
    classes.mkdir()
    names = ["TerminalBoundaryApControl", "NormalTargetCurrentGateControl"]
    commands, results = [], {}

    def run(argv: list[str], logname: str) -> str:
        result = subprocess.run(argv, cwd=root, text=True, capture_output=True, timeout=60)
        output = result.stdout + result.stderr
        log = work / logname
        log.write_text(output)
        commands.append({"argv": argv, "exitCode": result.returncode,
                         "log": str(log.relative_to(root)), "logSha256": sha(log)})
        if result.returncode:
            raise RuntimeError(output)
        return result.stdout

    run(["javac", "-J-Xmx256m", "-cp", cp, "-d", str(classes)] +
        [str(here / (name + ".java")) for name in names], "compile.log")
    for name in names:
        output = run(["java", "-Xmx256m", "-cp", str(classes) + ":" + cp, name], name + ".log")
        results[name] = json.loads(output.strip().splitlines()[-1])
    sources = [here / (name + ".java") for name in names] + [Path(__file__).resolve(), options]
    runtime = module / "src/main/kotlin/org/opentaint/dataflow/bidi"
    sources += [runtime / p for p in ["ap/ApOps.kt", "ap/EdgeApplication.kt",
                "ap/RestrictedInitialPolicy.kt", "ap/Demand.kt", "ap/Summary.kt",
                "store/RecordStore.kt", "interp/FormApplier.kt", "engine/RunMethodCallServices.kt"]]
    bytecode = module / "build/classes/kotlin/main/org/opentaint/dataflow/bidi/ap"
    sources += [bytecode / p for p in ["ApOps.class", "RestrictedInitialPolicy.class",
                "DemandKt.class", "SummaryKt.class", "EdgeApplicationKt.class"]]
    receipt = {
        "status": "PASS" if all(r["status"] == "PASS" for r in results.values()) else "FAILED",
        "scope": "Existing compiled AP primitives and bounded controls. No Target implementation or whole-engine run. Source and bytecode hashes are recorded; this checker does not prove bytecode was built from those source bytes.",
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "gitHead": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "compilerOptions": str(options), "classpathSha256": hashlib.sha256(cp.encode()).hexdigest(),
        "inputHashes": {str(p): sha(p) for p in sources},
        "results": results, "commands": commands,
    }
    (here / "checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": receipt["status"], "results": results}, indent=2))
    if receipt["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
