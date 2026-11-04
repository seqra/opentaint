#!/usr/bin/env python3
"""Check finite output-row batching; no Kotlin/AP/index proof or experiment."""
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
    module = importlib.util.spec_from_file_location('row_batching_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(module)
    module.loader.exec_module(scanner)
    source = HERE / 'OutputRowBatching.lean'
    pins_path = HERE / 'reference-source-pins.json'
    pins = json.loads(pins_path.read_text())
    assert pins['selection'] == 'PROPOSAL_MODEL_ONLY'
    assert pins['productionVerified'] is False and pins['kotlinAdapterVerified'] is False
    for name, expected in pins['sources'].items():
        value = subprocess.check_output(['git', 'show', pins['baselineRevision'] + ':' + name], cwd=ROOT)
        assert hashlib.sha256(value).hexdigest() == expected, name
        assert sha(ROOT / name) == expected, name
    clean = scanner.uncomment(source.read_text())
    assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b', clean)
    assert re.findall(r'^import\s+(\S+)', clean, re.M) == ['Std']
    declarations, count = scanner.declarations(source.read_text())
    declarations += ['OutputRowBatching.PairedRow', 'OutputRowBatching.PairedRow.mk',
                     'OutputRowBatching.PairedRow.ordinal', 'OutputRowBatching.PairedRow.payload']
    inputs = [source, HERE / 'README.md', HERE / 'REPORT.md', HERE / 'check.py',
              HERE / '.gitignore', pins_path, ROOT / 'spec/proof-guide.md',
              ROOT / 'spec/impl-proposal-guide.md', ROOT / 'spec/lean/lean-toolchain', scanner_path]
    inputs += [ROOT / name for name in pins['sources']]
    before = {str(path.relative_to(ROOT)): sha(path) for path in inputs}
    assert (ROOT / 'spec/lean/lean-toolchain').read_text().strip() == TOOLCHAIN
    lean = shutil.which('lean')
    assert lean
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version = subprocess.check_output([lean, '--version'], text=True, env=env).strip()
    assert re.search(r'version 4\.33\.1\b', version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    work = HERE / '.verification' / stamp
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

    run([lean, '-j', '1', '-M', '900', '-o', str(work / 'OutputRowBatching.olean'), str(source)],
        'OutputRowBatching.log', HERE)
    audit = work / 'Audit.lean'
    audit.write_text('import OutputRowBatching\n' + ''.join('#print axioms ' + name + '\n' for name in declarations))
    output = run([lean, '-j', '1', '-M', '900', str(audit)], 'Audit.log', work)
    audited = set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", output))
    assert audited == set(declarations)
    axioms = set()
    for group in re.findall(r'depends on axioms: \[([^\]]*)\]', output):
        axioms.update(value.strip() for value in group.split(',') if value.strip())
    assert axioms <= {'propext', 'Quot.sound'}
    (HERE / 'audit.txt').write_text(output)
    assert before == {str(path.relative_to(ROOT)): sha(path) for path in inputs}, 'Inputs changed during check'
    receipt = dict(
        status='PROPOSAL_OUTPUT_ROW_BATCHING_MODEL_PASS', selection='PROPOSAL_MODEL_ONLY',
        kotlinAdapterVerified=False, nativeAPSemanticsVerified=False, nativeIndexCompletenessVerified=False,
        sparseIndexImplementationVerified=False, fullLoopObservationEquivalenceVerified=False,
        implementationChanged=False, implementationExperimentsRun=False, productionVerifiedByKernel=False,
        wholeDriverConvergenceProved=False, projectQualityOrSpeedupMeasured=False,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), toolchain=TOOLCHAIN, leanVersion=version,
        moduleCount=1, theoremCount=count, auditedPublicDeclarationCount=len(declarations),
        declarations=declarations, axioms=sorted(axioms), noChoiceOrUnprovedAxioms=True,
        allExplicitPublicDefinitionsAndTheoremsAudited=True, inputsStable=True, inputHashes=before,
        baselineRevision=pins['baselineRevision'], referenceSourceRole=pins['sourceRole'],
        portableAudit=dict(path=str((HERE / 'audit.txt').relative_to(ROOT)), sha256=sha(HERE / 'audit.txt')),
        logs={str((work / name).relative_to(ROOT)): sha(work / name)
              for name in ['OutputRowBatching.log', 'Audit.lean', 'Audit.log']},
        limits=[
            'Native select, complete paired-row acceptance, per-row whole-bucket pack/cut and downstream ordered union are identical opaque functions on both sides.',
            'The dense scalar-column transpose proves ordered row grouping, not a production sparse posting implementation or its index completeness.',
            'False candidate cells must have native None selection; native AP/path/mark/layer/protection adapter evidence is still required.',
            'Posting k<=N is only a candidate-enumeration count; index construction, trie nodes, stable order, native work and output width remain separate costs.',
            'Both posting counts use the same whole-row/member-ordinal occurrence universe, not distinct native owner IDs versus expanded ND plan ordinals.',
            'No limit distribution, independent ND arm execution, field policy, ZERO/Target/source permission change or native conclusion equivalence is assumed.',
            'No Kotlin changes, Gradle/analyzer/profile experiments, project quality claim or speedup measurement are part of this package.'
        ])
    (HERE / 'checks.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in [
        'status', 'moduleCount', 'theoremCount', 'auditedPublicDeclarationCount', 'axioms', 'inputsStable']}, indent=2))


if __name__ == '__main__':
    main()
