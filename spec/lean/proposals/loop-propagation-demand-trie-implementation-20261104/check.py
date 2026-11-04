#!/usr/bin/env python3
"""Check only the new implementation-proposal delta; no native or older-model runs."""
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
MODULES = ['ProgramDedup', 'BoundaryFilter', 'CandidateJoin']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    scanner_path = ROOT / 'spec/lean/proposals/call-stage-result-merging-analysis-20261101/check.py'
    module = importlib.util.spec_from_file_location('loop_propagation_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(module)
    module.loader.exec_module(scanner)
    pins_path = HERE / 'reference-source-pins.json'
    pins = json.loads(pins_path.read_text())
    assert pins['selection'] == 'IMPLEMENTATION_PROPOSAL_MODEL_ONLY'
    assert pins['productionVerified'] is False and pins['kotlinAdapterVerified'] is False
    assert pins['relatedProofsImported'] is False and pins['relatedProofReceiptsRewritten'] is False
    for name, expected in pins['sources'].items():
        value = subprocess.check_output(['git', 'show', pins['baselineRevision'] + ':' + name], cwd=ROOT)
        assert hashlib.sha256(value).hexdigest() == expected, name
        assert sha(ROOT / name) == expected, name
    for name, expected in pins['relatedProofReceipts'].items():
        assert sha(ROOT / name) == expected, name
    declarations, counts = [], {}
    for name in MODULES:
        source = HERE / (name + '.lean')
        clean = scanner.uncomment(source.read_text())
        assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b', clean)
        assert re.findall(r'^import\s+(\S+)', clean, re.M) == ['Std']
        names, counts[name] = scanner.declarations(source.read_text())
        declarations += names
    explicit_types = {
        'ProgramDedup.Packet': ['mk', 'payload', 'protection'],
        'BoundaryFilter.Endpoint': ['local', 'zero', 'static', 'argument', 'receiver', 'returned', 'exception'],
        'BoundaryFilter.Direction': ['forward', 'reverse'],
        'BoundaryFilter.Relation': ['mk', 'premise', 'conclusion'],
        'BoundaryFilter.DataPacket': ['mk', 'endpoint', 'ordinaryPayload', 'protection'],
        'BoundaryFilter.Output': ['data', 'target', 'request', 'staticEffect'],
        'BoundaryFilter.Route': ['repeat', 'leave'],
    }
    for owner, children in explicit_types.items():
        declarations += [owner] + [owner + '.' + child for child in children]
    inputs = [HERE / (name + '.lean') for name in MODULES]
    inputs += [HERE / 'README.md', HERE / 'REPORT.md', HERE / 'check.py', HERE / '.gitignore',
               pins_path, ROOT / 'spec/proof-guide.md', ROOT / 'spec/impl-proposal-guide.md',
               ROOT / 'spec/lean/lean-toolchain', scanner_path]
    inputs += [ROOT / name for name in pins['sources']] + [ROOT / name for name in pins['relatedProofReceipts']]
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

    for name in MODULES:
        run([lean, '-j', '1', '-M', '900', '-o', str(work / (name + '.olean')), str(HERE / (name + '.lean'))],
            name + '.log', HERE)
    audit = work / 'Audit.lean'
    audit.write_text(''.join('import ' + name + '\n' for name in MODULES) +
                     ''.join('#print axioms ' + name + '\n' for name in declarations))
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
        status='IMPLEMENTATION_PROPOSAL_LOOP_PROPAGATION_DELTA_PASS', selection='IMPLEMENTATION_PROPOSAL_MODEL_ONLY',
        kotlinAdapterVerified=False, nativeAPSemanticsVerified=False, nativeIndexCompletenessVerified=False,
        mutableLifecycleOrNDJoinVerified=False, fullLoopObservationEquivalenceVerified=False,
        implementationChanged=False, implementationExperimentsRun=False, productionVerifiedByKernel=False,
        wholeDriverConvergenceProved=False, projectQualityOrSpeedupMeasured=False,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), toolchain=TOOLCHAIN, leanVersion=version,
        moduleCount=len(MODULES), theoremCount=sum(counts.values()), moduleTheoremCounts=counts,
        auditedPublicDeclarationCount=len(declarations), declarations=declarations,
        axioms=sorted(axioms), noChoiceOrUnprovedAxioms=True,
        allExplicitPublicDefinitionsAndTheoremsAudited=True, inputsStable=True, inputHashes=before,
        baselineRevision=pins['baselineRevision'], referenceSourceRole=pins['sourceRole'],
        relatedProofReceiptsImported=False, relatedProofReceiptsRerun=False, relatedProofReceiptsRewritten=False,
        portableAudit=dict(path=str((HERE / 'audit.txt').relative_to(ROOT)), sha256=sha(HERE / 'audit.txt')),
        logs={str(path.relative_to(ROOT)): sha(path) for path in sorted(work.iterdir())
              if path.suffix in {'.lean', '.log'}},
        limits=[
            'Program identity means the same complete pure emitted stream in one fixed query context; native ID construction and ExactDemandResults correspondence remain adapter obligations.',
            'Eligibility precedes stable dedup; exact first payload order and finite protection-bit OR are proved, not merely shape/count equality.',
            'Mutable prepared-exit application still runs. Only DATA callbacks use the prepared token; Target/request/static effects preserve exact order.',
            'Whole-application omission requires the stronger pure DATA-only capability and is restricted to the already certified observer path.',
            'Forward destination is conclusion and reverse destination is premise. Native oriented base, actual route masks and synthetic/unknown fallbacks remain adapter obligations.',
            'Use exactly the certified directed interface routes, including represented repeat/leave routes; dynamic ActualStarts intersection remains an unproved native adapter obligation.',
            'Inverse candidate masks may omit only native None; actual mutable snapshots/versioning, ND AND joins, queued effects and native index completeness are unproved.',
            'No Kotlin change, Gradle/analyzer/profile experiment, whole-project quality, convergence, resource-limit equivalence or speedup is claimed.'
        ])
    (HERE / 'checks.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in [
        'status', 'moduleCount', 'theoremCount', 'moduleTheoremCounts',
        'auditedPublicDeclarationCount', 'axioms', 'inputsStable']}, indent=2))


if __name__ == '__main__':
    main()
