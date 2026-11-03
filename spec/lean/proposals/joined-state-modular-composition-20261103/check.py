#!/usr/bin/env python3
"""Check selected design port composition; no Kotlin/native/GC verification."""
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
    spec = importlib.util.spec_from_file_location('composition_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scanner)
    pins = json.loads((HERE / 'component-pins.json').read_text())
    assert pins['selection'] == 'SELECTED_DESIGN_COMPOSITION'
    assert pins['kotlinVerified'] is False and pins['gcVerified'] is False
    model = HERE / 'Composition.lean'
    clean = scanner.uncomment(model.read_text())
    assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b', clean)
    assert re.findall(r'^import\s+(\S+)', clean, re.M) == [
        'JoinedStateRelease', 'LoopQueryReuse', 'PackedStaticGuidance']
    declarations, theorem_count = scanner.declarations(model.read_text())
    inputs = {model, HERE/'check.py', HERE/'component-pins.json', HERE/'README.md', HERE/'REPORT.md',
              ROOT/'spec/proof-guide.md', ROOT/'spec/impl-proposal-guide.md',
              ROOT/'spec/lean/lean-toolchain', scanner_path}
    modules = []
    component_counts = []
    for component in pins['components']:
        package = ROOT/'spec/lean/proposals'/component['package']
        for rel, expected in component['files'].items():
            path = ROOT/rel
            assert sha(path) == expected, rel
            inputs.add(path)
        receipt = json.loads((package/'checks.json').read_text())
        assert receipt['status'].endswith('PASS') and receipt['inputsStable']
        assert receipt['noChoiceOrUnprovedAxioms']
        assert set(receipt['axioms']) <= {'propext', 'Quot.sound'}
        assert receipt['baselineRevision'] == pins['baselineRevision']
        assert receipt['theoremCount'] == component['theorems']
        assert receipt['auditedPublicDeclarationCount'] == component['declarations']
        for rel, expected in receipt['inputHashes'].items():
            path = ROOT/rel
            assert sha(path) == expected, rel
            inputs.add(path)
        module_source = package/(component['module']+'.lean')
        modules.append((component['module'], module_source))
        component_counts.append({key: component[key] for key in ['package','theorems','declarations']})
    before = {str(p.relative_to(ROOT)): sha(p) for p in sorted(inputs)}
    assert (ROOT/'spec/lean/lean-toolchain').read_text().strip() == TOOLCHAIN
    lean = shutil.which('lean')
    assert lean
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version = subprocess.check_output([lean, '--version'], text=True, env=env).strip()
    assert re.search(r'version 4\.33\.1\b', version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    work = ROOT/'spec/lean/.lake/verification/joined-state-modular-composition-20261103'/stamp
    work.mkdir(parents=True)
    env['LEAN_PATH'] = str(work)

    def one_cpu():
        if hasattr(os, 'sched_getaffinity'):
            os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})

    def run(command, name, cwd):
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                timeout=120, preexec_fn=one_cpu)
        (work/name).write_text(result.stdout)
        assert result.returncode == 0 and not re.search(r'\b(?:warning|error):', result.stdout), result.stdout
        return result.stdout

    for name, source in modules + [('Composition', model)]:
        run([lean, '-j', '1', '-M', '900', '-o', str(work/(name+'.olean')), str(source)], name+'.log', source.parent)
    audit = work/'Audit.lean'
    audit.write_text('import Composition\n' + ''.join('#print axioms '+n+'\n' for n in declarations))
    output = run([lean, '-j', '1', '-M', '900', str(audit)], 'Audit.log', work)
    audited = set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", output))
    assert audited == set(declarations)
    axioms = set()
    for group in re.findall(r'depends on axioms: \[([^\]]*)\]', output):
        axioms.update(x.strip() for x in group.split(',') if x.strip())
    assert axioms <= {'propext', 'Quot.sound'}
    (HERE/'audit.txt').write_text(output)
    assert before == {str(p.relative_to(ROOT)): sha(p) for p in sorted(inputs)}, 'Inputs changed during check'
    receipt = dict(
        status='SELECTED_DESIGN_MODULAR_COMPOSITION_PASS',
        selection='SELECTED_DESIGN_COMPOSITION_ONLY',
        runtimeImplementationChanged=False, kotlinVerified=False, gcVerified=False,
        fullAPAdapterVerified=False, projectQualityOrSpeedupMeasured=False,
        wholeDriverConvergenceProved=False, resourceLimitOutcomeEquivalenceProved=False,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), toolchain=TOOLCHAIN,
        leanVersion=version, baselineRevision=pins['baselineRevision'],
        moduleCount=1, theoremCount=theorem_count,
        auditedPublicDeclarationCount=len(declarations), declarations=declarations,
        importedComponentModels=component_counts, axioms=sorted(axioms),
        noChoiceOrUnprovedAxioms=True, allExplicitPublicDefinitionsAndTheoremsAudited=True,
        inputsStable=True, inputHashes=before,
        portableAudit=dict(path=str((HERE/'audit.txt').relative_to(ROOT)), sha256=sha(HERE/'audit.txt')),
        logs={str(p.relative_to(ROOT)): sha(p) for p in sorted(work.iterdir()) if p.suffix in {'.log','.lean'}},
        prerequisites=[
            'Point 1 Kotlin seal preserves its complete retained read footprint and actual input owners.',
            'Ingest is the unchanged deterministic normalized ordered static source and bound-extra stream.',
            'Packed native indexes/callbacks realize point 3 exact complete ordered query oracle.',
            'Point 2 preparedPort preserves full enclosing observations under its native eligibility/fallback conditions.',
            'Exact frozen scope/ports/policy, full originals, layers, exclusions, protection and Target IDs are retained.',
            'Finite query programs and deterministic handoff/report functions consume those complete equal values.'
        ],
        limits=[
            'No Kotlin/native/concurrency/GC/canonical-reference proof follows from imported finite models.',
            'No project run, new experiment, resource-limit outcome, memory reclamation or speedup is proved.',
            'The composition adds no ZERO/Target/AP/ND/source-permission policy and verifies no archived ZERO draft.'
        ])
    (HERE/'checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['status','moduleCount','theoremCount',
        'auditedPublicDeclarationCount','axioms','inputsStable']},indent=2))


if __name__ == '__main__':
    main()
