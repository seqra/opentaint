#!/usr/bin/env python3
"""Check finite demand-prefix geometry and conditional scalar C2/search laws."""
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
    module = importlib.util.spec_from_file_location('demand_trie_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(module)
    module.loader.exec_module(scanner)
    source = HERE / 'DemandTriePrefix.lean'
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
    assert re.findall(r'^import\s+(\S+)', clean, re.M) == ['Std', 'Geometry']
    declarations, count = scanner.declarations(source.read_text())
    declarations += ['DemandTriePrefix.StrictCutCertificate', 'DemandTriePrefix.StrictCutCertificate.mk',
                     'DemandTriePrefix.StrictCutCertificate.keptPrefix', 'DemandTriePrefix.StrictCutCertificate.shorter',
                     'DemandTriePrefix.StrictCutCertificate.firstNew', 'DemandTriePrefix.StrictCutCertificate.distinct',
                     'DemandTriePrefix.InitialTail', 'DemandTriePrefix.InitialTail.exact',
                     'DemandTriePrefix.InitialTail.star', 'DemandTriePrefix.InitialTail.may']
    geometry = ROOT / pins['importedGeometry']
    dependency_clean = scanner.uncomment(geometry.read_text())
    assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b', dependency_clean)
    assert re.findall(r'^import\s+(\S+)', dependency_clean, re.M) == ['Init']
    _, dependency_count = scanner.declarations(geometry.read_text())
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

    for name, path in [('Geometry', geometry), ('DemandTriePrefix', source)]:
        run([lean, '-j', '1', '-M', '900', '-o', str(work / (name + '.olean')), str(path)], name + '.log', path.parent)
    audit = work / 'Audit.lean'
    audit.write_text('import DemandTriePrefix\n' + ''.join('#print axioms ' + name + '\n' for name in declarations))
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
        status='PROPOSAL_DEMAND_TRIE_PREFIX_MODEL_PASS', selection='PROPOSAL_MODEL_ONLY',
        kotlinAdapterVerified=False, nativeAPSemanticsVerified=False, nativeIndexCompletenessVerified=False,
        universalTrieC2CertificateVerified=False, universalMinimalityVerified=False,
        fullLoopObservationEquivalenceVerified=False, sparseTrieRuntimeComplexityVerified=False,
        implementationChanged=False, implementationExperimentsRun=False, productionVerifiedByKernel=False,
        wholeDriverConvergenceProved=False, projectQualityOrSpeedupMeasured=False,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), toolchain=TOOLCHAIN, leanVersion=version,
        moduleCount=1, importedReferenceModuleCount=1, importedGeometryTheoremCount=dependency_count,
        theoremCount=count, auditedPublicDeclarationCount=len(declarations), declarations=declarations,
        axioms=sorted(axioms), noChoiceOrUnprovedAxioms=True,
        allExplicitPublicDefinitionsAndTheoremsAudited=True, inputsStable=True, inputHashes=before,
        baselineRevision=pins['baselineRevision'], referenceSourceRole=pins['sourceRole'],
        portableAudit=dict(path=str((HERE / 'audit.txt').relative_to(ROOT)), sha256=sha(HERE / 'audit.txt')),
        logs={str((work / name).relative_to(ROOT)): sha(work / name)
              for name in ['Geometry.log', 'DemandTriePrefix.log', 'Audit.lean', 'Audit.log']},
        limits=[
            'Complete compatible demand paths are supplied after correct owner/scope/route/direction/base/FULL-mark filtering; actual index completeness is not proved.',
            'The precision forest must apply existing native pre-admission guards per (scope,base), including MethodBlockRuntime.keepLocalConclusion before DemandStore; rejected local scopes cannot witness and unknown guard views require native fallback.',
            'Node-walk/full-LCP equality, first distinguishing fields, terminal payloads, prefix identity and deepest-demand+1 bound are proved in counted nonstatic geometry.',
            'Conditional C2 image proof is scalar concrete FULL, empty E, valid bounded EXACT/ANY actual and demand paths; FLOW/STAR/MUST/static/packed/native correspondence is excluded.',
            'A finite geometric certificate establishes C2 preservation; no universal theorem claims every trie proposal supplies that certificate.',
            'Constructive max-LCP witness plus constant ANY/MAY/DEMAND emission range and baseline absence can certify skipping earlier candidates; native family/label correspondence remains required.',
            'Raw MAY counterexample disproves universal trie minimality; unsupported or uncertified cases keep native ascending search and candidate checks.',
            'No full AL/Target/LoopObservation equality, runtime Kotlin change, Gradle/analyzer/profile experiment, project quality or speedup is claimed.'
        ])
    (HERE / 'checks.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in [
        'status', 'moduleCount', 'importedReferenceModuleCount', 'theoremCount',
        'auditedPublicDeclarationCount', 'axioms', 'inputsStable']}, indent=2))


if __name__ == '__main__':
    main()
