#!/usr/bin/env python3
"""Run the OWASP doSomething baseline using the saved benchmark project and capture agent."""

import argparse
from collections import defaultdict
import gzip
import json
from pathlib import Path
import re
import subprocess

ENTRY = "org.owasp.benchmark.testcode.BenchmarkTest01000#doPost"
HELPER = (
    "org.owasp.benchmark.testcode.BenchmarkTest01000$Test#doSomething"
    "(javax.servlet.http.HttpServletRequest, java.lang.String) [{}]"
)
ASM_EXPORTS = (
    "--add-exports=java.base/jdk.internal.org.objectweb.asm=ALL-UNNAMED",
    "--add-exports=java.base/jdk.internal.org.objectweb.asm.commons=ALL-UNNAMED",
)


def verify(output: Path):
    stdout = (output / "owasp-entry-console.log").read_text()
    assert "RUN101_TEST_POLICY lastForwardRun=101" in stdout
    assert re.findall(r"BIDI_RUN_END run=(\d+) status=COMPLETE", stdout) == [
        str(i) for i in range(1, 102)
    ]
    assert "BIDI_ANALYSIS_END run=101 status=COMPLETE reason=RUN_LIMIT" in stdout
    assert "BIDI_REPORT_STATISTICS run=101 reason=RUN_LIMIT confirmed=2 provisional=0" in stdout

    frontiers = defaultdict(set)
    with gzip.open(output / "trace.jsonl.gz", "rt") as capture:
        for line in capture:
            row = json.loads(line)
            if row["event"] == "PROJECTION_DATA" and row["method"] == HELPER:
                frontiers[row["run"]].add(json.dumps(
                    (row["scope"], row["entry"], row["exit"]), sort_keys=True
                ))
            if row["event"] == "END":
                assert row["errors"] == 0
    for first, count in [(7, 6), (8, 8)]:
        assert len(frontiers[first]) == count, (first, frontiers[first])
        for run in range(first + 2, 102, 2):
            assert frontiers[first] == frontiers[run], (first, run)
    print("run-101 RUN_LIMIT with two confirmed. Repeated helper pairs from run-7 F / run-8 B (6 / 8).")


def run(project: Path, capture_agent: Path, output: Path):
    root = Path(__file__).resolve().parents[3]
    agent = output / "run101.jar"
    manifest = output / "manifest"
    classes = output / "classes"
    classes.mkdir()
    subprocess.run(["javac", ASM_EXPORTS[0], "-d", classes,
                    Path(__file__).with_name("Run101.java")], check=True)
    manifest.write_text("Premain-Class: Run101\n")
    subprocess.run(["jar", "cfm", agent, manifest, "-C", classes, "."], check=True)
    jvm = ["-Xmx8g", "-Dopentaint.bidi.run1MarkMode=FULL",
           "-Dopentaint.bidi.fieldLimitSchedule=REPEAT_RUN1", *ASM_EXPORTS,
           f"-javaagent:{agent}", f"-javaagent:{capture_agent}={output / 'trace.jsonl.gz'}",
           "-Ddemand.capture.firstBarrier=1", "-Ddemand.capture.lastBarrier=101",
           f"-Ddemand.capture.focus={HELPER}", "-Ddemand.capture.savedProviders=true"]
    args = ["--project", str(project), "--output-dir", str(output / "reports"),
            "--ifds-analysis-timeout", "1000", "--logs-file", str(output / "analyzer.log"),
            "--verbosity", "debug", "--semgrep-rule-set", str(root / "rules/ruleset"),
            "--sarif-generate-fingerprint", "--ifds-bidirectional",
            "--debug-run-analysis-on-selected-entry-points", ENTRY]
    init = output / "run101.init.gradle"
    init.write_text(f"""gradle.projectsEvaluated {{
  if (rootProject.name != "opentaint-jvm-sast") return
  rootProject.tasks.named("runProjectAnalyzer", JavaExec).configure {{
    jvmArgs = {json.dumps(jvm).replace('$', chr(92) + '$')}
    args = {json.dumps(args)}
  }}
}}
""")
    with (output / "owasp-entry-console.log").open("w") as log:
        subprocess.run([root / "core/gradlew", "-p", root / "core", ":runProjectAnalyzer",
                        "--console=plain", "--offline", "-I", init,
                        "-x", ":opentaint-ir:go:buildGoServer"], stdout=log,
                       stderr=subprocess.STDOUT, check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--project", type=Path)
    parser.add_argument("--capture-agent", type=Path)
    options = parser.parse_args()
    if bool(options.project) != bool(options.capture_agent):
        parser.error("supply both --project and --capture-agent to run, or neither to verify")
    output = options.output.resolve()
    if options.project:
        output.mkdir(parents=True)
        run(options.project.resolve(), options.capture_agent.resolve(), output)
    verify(output)
