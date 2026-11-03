#!/usr/bin/env python3
"""Check unselected exact candidate-oracle pruning laws, not the Kotlin implementation."""
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
    module = importlib.util.spec_from_file_location('candidate_static_pruning_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(module)
    module.loader.exec_module(scanner)
    source = HERE / 'CandidateStaticPruning.lean'
    selected = HERE / 'PROPOSAL.md'
    proposal = selected
    assert 'Status: **UNSELECTED**' in selected.read_text()
    pins = json.loads((HERE / 'reference-source-pins.json').read_text())
    assert pins['productionVerified'] is False
    assert pins['selection'] == 'UNSELECTED'
    assert pins['kotlinOracleEquivalenceProved'] is False
    baseline = pins['baselineRevision']
    for name, expected in pins['sources'].items():
        value = subprocess.check_output(['git', 'show', baseline + ':' + name], cwd=ROOT)
        assert hashlib.sha256(value).hexdigest() == expected, name
    clean = scanner.uncomment(source.read_text())
    assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b', clean)
    assert re.findall(r'^import\s+(\S+)', clean, re.M) == ['Std']
    declarations, count = scanner.declarations(source.read_text())
    inputs = [source, selected, proposal, HERE / 'README.md', HERE / 'REPORT.md', HERE / 'check.py',
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
    work = ROOT / 'spec/lean/.lake/verification/candidate-directed-static-pruning-20261103' / stamp
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

    run([lean, '-j', '1', '-M', '768', '-o', str(work / 'CandidateStaticPruning.olean'), str(source)],
        'CandidateStaticPruning.log', HERE)
    audit = work / 'Audit.lean'
    audit.write_text('import CandidateStaticPruning\n' + ''.join('#print axioms ' + name + '\n' for name in declarations))
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
        status='UNSELECTED_CONDITIONAL_FINITE_MODEL_PASS', selection='UNSELECTED_CANDIDATE_DIRECTED_STATIC_PRUNING',
        kotlinOracleEquivalenceProved=False, oracleInternalComplexityProved=False,
        implementationSelected=False, runtimeImplementationChanged=False,
        productionVerifiedByKernel=False, fullAPAdapterVerified=False,
        wholeDriverConvergenceProved=False, projectQualityOrSpeedupMeasured=False,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), toolchain=TOOLCHAIN, leanVersion=version,
        moduleCount=1, theoremCount=count, auditedPublicDeclarationCount=len(declarations),
        declarations=declarations, axioms=sorted(axioms), noChoiceOrUnprovedAxioms=True,
        allExplicitPublicDefinitionsAndTheoremsAudited=True, inputsStable=True, inputHashes=before,
        referenceSourceRole=pins['sourceRole'], baselineRevision=baseline,
        portableAudit=dict(path=str((HERE / 'audit.txt').relative_to(ROOT)), sha256=sha(HERE / 'audit.txt')),
        logs={str((work / name).relative_to(ROOT)): sha(work / name)
              for name in ['CandidateStaticPruning.log', 'Audit.lean', 'Audit.log']},
        limits=[
            'Oracle equivalence is an explicit theorem prerequisite; no Kotlin query/index adapter is proved.',
            'The executable exact reference oracle enumerates old survivors and claims no efficiency benefit.',
            'Finite rows follow existing valid runtime-domain filters; AP algebra and live packed-store enumeration are not kernel verified.',
            'Both layers/protection, FLOW mx removal, pair-tail normalization and MUST to ANY are modeled without a coverage substitution.',
            'Observed/lost raw IDs and order plus peak metadata are equal conditionally; lifecycle freeze idempotence is not modeled.',
            'Only caller unrelated-row materializations are bounded; oracle internals, cancellation, exceptions and project speedup remain unproved.',
            'No native/Gradle/analyzer/JFR/heap experiment or runtime policy change is part of this package.'
])
    (HERE / 'checks.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in [
        'status', 'selection', 'moduleCount', 'theoremCount',
        'auditedPublicDeclarationCount', 'axioms', 'inputsStable']}, indent=2))


if __name__ == '__main__':
    main()
