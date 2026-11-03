#!/usr/bin/env python3
"""Check selected scoped physical-request transport laws, not the Kotlin implementation."""
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
    module = importlib.util.spec_from_file_location('scoped_request_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(module)
    module.loader.exec_module(scanner)
    source = HERE / 'ScopedRequestClimbs.lean'
    selected = ROOT / 'spec/scoped-request-climbs.md'
    proposal = selected
    assert 'selected correctness correction' in selected.read_text()
    pins = json.loads((HERE / 'reference-source-pins.json').read_text())
    assert pins['productionVerified'] is False
    baseline = pins['baselineRevision']
    for name, expected in pins['sources'].items():
        value = subprocess.check_output(['git', 'show', baseline + ':' + name], cwd=ROOT)
        assert hashlib.sha256(value).hexdigest() == expected, name
    clean = scanner.uncomment(source.read_text())
    assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b', clean)
    assert re.findall(r'^import\s+(\S+)', clean, re.M) == ['Std']
    declarations, count = scanner.declarations(source.read_text())
    inputs = [source, selected, proposal, HERE / 'README.md', HERE / 'check.py',
              HERE / 'reference-source-pins.json', ROOT / 'spec/proof-guide.md',
              ROOT / 'spec/lean/lean-toolchain', scanner_path]
    before = {str(path.relative_to(ROOT)): sha(path) for path in inputs}
    assert (ROOT / 'spec/lean/lean-toolchain').read_text().strip() == TOOLCHAIN
    lean = shutil.which('lean')
    assert lean
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version = subprocess.check_output([lean, '--version'], text=True, env=env).strip()
    assert re.search(r'version 4\.33\.1\b', version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    work = ROOT / 'spec/lean/.lake/verification/scoped-request-climbs-20261103' / stamp
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

    run([lean, '-j', '1', '-M', '768', '-o', str(work / 'ScopedRequestClimbs.olean'), str(source)],
        'ScopedRequestClimbs.log', HERE)
    audit = work / 'Audit.lean'
    audit.write_text('import ScopedRequestClimbs\n' + ''.join('#print axioms ' + name + '\n' for name in declarations))
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
        status='SELECTED_FINITE_MODEL_PASS', selection='SELECTED_SCOPED_REQUEST_TRANSPORT_CORRECTION',
        productionVerifiedByKernel=False, fullAPAdapterVerified=False,
        wholeDriverConvergenceProved=False, projectQualityOrSpeedupMeasured=False,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), toolchain=TOOLCHAIN, leanVersion=version,
        moduleCount=1, theoremCount=count, auditedPublicDeclarationCount=len(declarations),
        declarations=declarations, axioms=sorted(axioms), noChoiceOrUnprovedAxioms=True,
        allExplicitPublicDefinitionsAndTheoremsAudited=True, inputsStable=True, inputHashes=before,
        referenceSourceRole=pins['sourceRole'], baselineRevision=baseline,
        portableAudit=dict(path=str((HERE / 'audit.txt').relative_to(ROOT)), sha256=sha(HERE / 'audit.txt')),
        logs={str((work / name).relative_to(ROOT)): sha(work / name)
              for name in ['ScopedRequestClimbs.log', 'Audit.lean', 'Audit.log']},
        limits=[
            'Exact immutable slot matching is supplied unchanged, not proved.',
            'Batch and destination histories are finite executable lists; production packed mark storage is not verified.',
            'No proof of Kotlin actors, queue accounting, physical field matching or source rules.',
            'Immutable baseline blobs identify interfaces; current implementation and native validation are separate.',
            'Arrival-order law covers scoped request membership, not callback order or diagnostic counts.',
            'No claim of unchanged final AP stores, convergence, project quality or performance.'])
    (HERE / 'checks.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in [
        'status', 'selection', 'moduleCount', 'theoremCount',
        'auditedPublicDeclarationCount', 'axioms', 'inputsStable']}, indent=2))


if __name__ == '__main__':
    main()
