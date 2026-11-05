#!/usr/bin/env python3
"""Check proposal models and pin their boundary; do not run the analyzer."""
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
RUNTIME = '52f32dd437d438aec4a700a02c18d94c31d58093'
TOOLCHAIN = 'leanprover/lean4:v4.33.1'
MODULES = ['Canonical', 'Relations', 'Matching', 'Reachability']
PROPOSAL = ROOT / 'docs/design/bidirectional-canonical-facts-normal-relations-directional-inside-implementation-20261105.md'
BASE = 'core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/'
CONTEXT = [BASE + name for name in [
    'ap/Groups.kt', 'ap/Reference.kt', 'ap/Summary.kt', 'ap/RestrictedInitialPolicy.kt',
    'ap/ApOps.kt', 'store/FlowBackedSummaries.kt', 'store/RunSummaries.kt',
    'store/DiagonalRelations.kt', 'store/RecordStore.kt', 'engine/PublicationIndex.kt',
    'engine/SummaryStorage.kt', 'engine/PersistedSummaryReplay.kt',
    'engine/LocalRelationApplication.kt', 'engine/MethodBlockRuntime.kt',
    'engine/LoopConsumerObservation.kt', 'engine/LoopOutputRestriction.kt',
    'engine/RunMethodCallServices.kt', 'driver/HandOff.kt', 'driver/BlockHandOff.kt',
]]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    scanner_path = ROOT / 'spec/lean/proposals/call-stage-result-merging-analysis-20261101/check.py'
    spec = importlib.util.spec_from_file_location('proposal_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scanner)
    declarations, counts = [], {}
    for name in MODULES:
        raw = (HERE / (name + '.lean')).read_text()
        clean = scanner.uncomment(raw)
        assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b', clean)
        assert all(i in ['Std'] + MODULES for i in re.findall(r'^import\s+(\S+)', clean, re.M))
        names, counts[name] = scanner.declarations(raw)
        declarations += names
    assert len(declarations) == len(set(declarations)), 'Overlapping public model names'
    for name in CONTEXT:
        original = subprocess.check_output(['git', 'show', RUNTIME + ':' + name], cwd=ROOT)
        assert hashlib.sha256(original).hexdigest() == digest(ROOT / name), name
    inputs = [HERE / (n + '.lean') for n in MODULES]
    inputs += sorted(HERE.glob('native-overlap-*'))
    inputs += [HERE / 'README.md', HERE / 'check.py', PROPOSAL, scanner_path,
               ROOT / 'spec/proof-guide.md', ROOT / 'spec/impl-proposal-guide.md',
               ROOT / 'spec/lean/lean-toolchain'] + [ROOT / n for n in CONTEXT]
    before = {str(p.relative_to(ROOT)): digest(p) for p in inputs}
    assert (ROOT / 'spec/lean/lean-toolchain').read_text().strip() == TOOLCHAIN
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    lean = shutil.which('lean')
    assert lean
    version = subprocess.check_output([lean, '--version'], env=env, text=True).strip()
    assert re.search(r'version 4\.33\.1\b', version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    work = ROOT / 'spec/lean/.lake/verification/flow-antichains-directional-matching-20261105' / ('all-' + stamp)
    work.mkdir(parents=True)
    env['LEAN_PATH'] = str(work)

    def limits():
        if hasattr(os, 'sched_getaffinity'):
            os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})

    def run(command, log):
        result = subprocess.run(command, cwd=HERE, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                timeout=180, preexec_fn=limits)
        (work / log).write_text(result.stdout)
        assert result.returncode == 0 and not re.search(r'\b(?:warning|error):', result.stdout), result.stdout
        return result.stdout

    for name in MODULES:
        run([lean, '-j', '1', '-M', '900', '-o', str(work / (name + '.olean')),
             str(HERE / (name + '.lean'))], name + '.log')
    audit = work / 'Audit.lean'
    audit.write_text(''.join('import ' + n + '\n' for n in MODULES) +
                     ''.join('#print axioms ' + n + '\n' for n in declarations))
    out = run([lean, '-j', '1', '-M', '900', str(audit)], 'Audit.log')
    actual = set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", out))
    assert actual == set(declarations)
    axioms = set()
    for group in re.findall(r'depends on axioms: \[([^\]]*)\]', out):
        axioms.update(v.strip() for v in group.split(',') if v.strip())
    assert axioms <= {'propext', 'Quot.sound'}
    (HERE / 'audit.txt').write_text(out)
    assert before == {str(p.relative_to(ROOT)): digest(p) for p in inputs}, 'Input changed during check'
    receipt = {
        'status': 'SELECTED_PROPOSAL_MODELS_PASS',
        'selection': 'CANONICAL_FACTS_NORMAL_RELATIONS_OPPOSITE_STAR_INSIDE',
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'runtimeReference': RUNTIME, 'implementationChanged': False,
        'toolchain': TOOLCHAIN, 'leanVersion': version,
        'moduleCount': len(MODULES), 'theoremCount': sum(counts.values()),
        'moduleTheoremCounts': counts, 'auditedExplicitDefinitionAndTheoremCount': len(declarations),
        'declarations': declarations, 'axioms': sorted(axioms),
        'noChoiceOrUnprovedAxioms': True, 'inputsStable': True, 'inputHashes': before,
        'nativeKotlinAdapterVerified': False, 'wholeEngineFindingEquivalenceProved': False,
        'wholeDriverConvergenceProved': False, 'projectPerformanceMeasured': False,
        'proofBoundary': [
            'Spatial laws use exact concrete-location regions within compatible finite header cells; packed DAG and native mark/protection correspondence need adapter tests.',
            'Canonical C2 input is the selected new policy; equality to old redundant-leaf C2 output is not claimed.',
            'NORMAL relation factoring, cover queries, antichain and concrete finite-path preservation are proved in the empty-field-exclusion aligned STAR cell.',
            'Matching proves the selected ordered filter relative to supplied native eligibility, not universal report preservation after narrowing saved-direct matches.',
            'Native reverse-MUST view provenance, overlap projection, typed application, actor ownership, publication settlement, C5 and handoff need native integration checks.',
            'No analyzer implementation, real-project experiment, quality acceptance, or speedup is included.'
        ],
        'audit': {'path': str((HERE / 'audit.txt').relative_to(ROOT)), 'sha256': digest(HERE / 'audit.txt')},
        'logs': {str(p.relative_to(ROOT)): digest(p) for p in sorted(work.iterdir()) if p.suffix in {'.lean', '.log'}},
    }
    (HERE / 'checks.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in ['status', 'moduleCount', 'theoremCount',
          'moduleTheoremCounts', 'auditedExplicitDefinitionAndTheoremCount', 'axioms', 'inputsStable']}, indent=2))


if __name__ == '__main__':
    main()
