#!/usr/bin/env python3
"""Check the selected joined-state release design model; no Kotlin verification."""
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'spec/lean/lean-toolchain').is_file())
TOOLCHAIN = 'leanprover/lean4:v4.33.1'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    scanner_path = ROOT / 'spec/lean/proposals/call-stage-result-merging-analysis-20261101/check.py'
    module = importlib.util.spec_from_file_location('selected_joined_release_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(module)
    module.loader.exec_module(scanner)
    source = HERE / 'JoinedStateRelease.lean'
    selected = ROOT / 'docs/design/bidirectional-joined-state-release-design-20261103.md'
    assert 'Status: **SELECTED DESIGN; not implemented**' in selected.read_text()
    pins = json.loads((HERE / 'reference-source-pins.json').read_text())
    assert pins['implementationChanged'] is False
    assert pins['selection'] == 'SELECTED_DESIGN'
    assert pins['kotlinReadFootprintProved'] is False
    baseline = pins['baselineRevision']
    for name, expected in pins['sources'].items():
        value = subprocess.check_output(['git', 'show', baseline + ':' + name], cwd=ROOT)
        assert hashlib.sha256(value).hexdigest() == expected, name
    clean = scanner.uncomment(source.read_text())
    assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b', clean)
    assert re.findall(r'^import\s+(\S+)', clean, re.M) == ['Std']
    declarations, count = scanner.declarations(source.read_text())
    inputs = [source, selected, HERE / 'README.md', HERE / 'REPORT.md', HERE / 'check.py',
              HERE / 'reference-source-pins.json', ROOT / 'spec/proof-guide.md',
              ROOT / 'spec/lean/lean-toolchain', ROOT / 'spec/impl-proposal-guide.md', scanner_path]
    before = {str(path.relative_to(ROOT)): sha(path) for path in inputs}
    assert (ROOT / 'spec/lean/lean-toolchain').read_text().strip() == TOOLCHAIN
    lean = shutil.which('lean')
    assert lean
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version = subprocess.check_output([lean, '--version'], text=True, env=env).strip()
    assert re.search(r'version 4\.33\.1\b', version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    work = ROOT / 'spec/lean/.lake/verification/joined-state-release-selected-design-20261103' / stamp
    work.mkdir(parents=True)
    env['LEAN_PATH'] = str(work)

    def one_cpu():
        if hasattr(os, 'sched_getaffinity'):
            os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})

    def run(command, name, cwd):
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                timeout=120, preexec_fn=one_cpu)
        (work / name).write_text(result.stdout)
        assert result.returncode == 0 and not re.search(r'\b(?:warning|error):', result.stdout), result.stdout
        return result.stdout

    run([lean, '-j', '1', '-M', '768', '-o', str(work / 'JoinedStateRelease.olean'), str(source)],
        'JoinedStateRelease.log', HERE)
    audit = work / 'Audit.lean'
    audit.write_text('import JoinedStateRelease\n' + ''.join('#print axioms ' + name + '\n' for name in declarations))
    output = run([lean, '-j', '1', '-M', '768', str(audit)], 'Audit.log', work)
    audited = set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", output))
    assert audited == set(declarations)
    axioms = set()
    for group in re.findall(r'depends on axioms: \[([^\]]*)\]', output):
        axioms.update(value.strip() for value in group.split(',') if value.strip())
    assert axioms <= {'propext', 'Quot.sound'}
    (HERE / 'audit.txt').write_text(output)
    assert before == {str(path.relative_to(ROOT)): sha(path) for path in inputs}, 'Inputs changed during check'
    receipt = dict(
        status='SELECTED_DESIGN_CONDITIONAL_FINITE_MODEL_PASS', selection='SELECTED_JOINED_STATE_RELEASE_DESIGN',
        kotlinReadFootprintProved=False, garbageCollectorReachabilityProved=False,
        designSelected=True, runtimeImplementationChanged=False,
        productionVerifiedByKernel=False, fullAPAdapterVerified=False,
        wholeDriverConvergenceProved=False, projectQualityOrSpeedupMeasured=False,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), toolchain=TOOLCHAIN, leanVersion=version,
        moduleCount=1, theoremCount=count, auditedPublicDeclarationCount=len(declarations),
        declarations=declarations, axioms=sorted(axioms), noChoiceOrUnprovedAxioms=True,
        allExplicitPublicDefinitionsAndTheoremsAudited=True, inputsStable=True, inputHashes=before,
        referenceSourceRole=pins['sourceRole'], baselineRevision=baseline,
        portableAudit=dict(path=str((HERE / 'audit.txt').relative_to(ROOT)), sha256=sha(HERE / 'audit.txt')),
        logs={str((work / name).relative_to(ROOT)): sha(work / name)
              for name in ['JoinedStateRelease.log', 'Audit.lean', 'Audit.log']},
        limits=[
            'A J-only pure binder is the explicit model prerequisite; Kotlin retained read closure is not proved.',
            'The closed post-join live-event protocol is modeled; Kotlin concurrency, queue quiescence and cancellation are not verified.',
            'Retained read projections/snapshots are preserved; JVM canonical reference identity and native adapters remain unproved.',
            'The model drops selected root references only; retained aliases may keep data reachable and no GC/free-byte claim is proved.',
            'Shared AP interners, IR and rewrite SoftManager are retained, with no clearing or replacement authorized.',
            'New-run failure publishes no handoff; preservation of prior accepted reports is an external driver prerequisite.',
            'No native/Gradle/analyzer/JFR/MAT experiment, runtime implementation, AP policy change, memory saving or speedup is part of this package.'
])
    (HERE / 'checks.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in [
        'status', 'selection', 'moduleCount', 'theoremCount',
        'auditedPublicDeclarationCount', 'axioms', 'inputsStable']}, indent=2))


if __name__ == '__main__':
    main()
