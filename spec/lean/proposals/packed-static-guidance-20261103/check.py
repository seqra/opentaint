#!/usr/bin/env python3
"""Check selected finite catalog design; do not run or verify Kotlin."""
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
    mod = importlib.util.spec_from_file_location('packed_guidance_scanner', scanner_path)
    scanner = importlib.util.module_from_spec(mod)
    mod.loader.exec_module(scanner)
    source = HERE / 'PackedStaticGuidance.lean'
    design = ROOT / 'docs/design/bidirectional-packed-static-guidance-design-20261103.md'
    assert '**Selected design. Not implemented.**' in design.read_text()
    pins = json.loads((HERE / 'reference-source-pins.json').read_text())
    assert pins['selection'] == 'SELECTED_DESIGN'
    assert pins['productionVerified'] is False
    assert pins['kotlinAdapterEquivalenceProved'] is False
    for name, expected in pins['sources'].items():
        value = subprocess.check_output(['git', 'show', pins['baselineRevision'] + ':' + name], cwd=ROOT)
        assert hashlib.sha256(value).hexdigest() == expected, name
    clean = scanner.uncomment(source.read_text())
    assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b', clean)
    assert re.findall(r'^import\s+(\S+)', clean, re.M) == ['Std']
    declarations, theorem_count = scanner.declarations(source.read_text())
    inputs = [source, design, HERE/'PROPOSAL.md', HERE/'README.md', HERE/'REPORT.md',
              HERE/'check.py', HERE/'reference-source-pins.json', ROOT/'spec/proof-guide.md',
              ROOT/'spec/impl-proposal-guide.md', ROOT/'spec/lean/lean-toolchain', scanner_path]
    before = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    assert (ROOT/'spec/lean/lean-toolchain').read_text().strip() == TOOLCHAIN
    lean = shutil.which('lean')
    assert lean
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version = subprocess.check_output([lean, '--version'], text=True, env=env).strip()
    assert re.search(r'version 4\.33\.1\b', version)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    work = ROOT/'spec/lean/.lake/verification/packed-static-guidance-20261103'/stamp
    work.mkdir(parents=True)
    env['LEAN_PATH'] = str(work)

    def one_cpu():
        if hasattr(os, 'sched_getaffinity'):
            os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})

    def run(command, name, cwd):
        result = subprocess.run(command, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=120, preexec_fn=one_cpu)
        (work/name).write_text(result.stdout)
        assert result.returncode == 0 and not re.search(r'\b(?:warning|error):', result.stdout), result.stdout
        return result.stdout

    run([lean, '-j', '1', '-M', '768', '-o', str(work/'PackedStaticGuidance.olean'), str(source)],
        'PackedStaticGuidance.log', HERE)
    audit = work/'Audit.lean'
    audit.write_text('import PackedStaticGuidance\n' + ''.join('#print axioms ' + n + '\n' for n in declarations))
    output = run([lean, '-j', '1', '-M', '768', str(audit)], 'Audit.log', work)
    audited = set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", output))
    assert audited == set(declarations)
    axioms = set()
    for group in re.findall(r'depends on axioms: \[([^\]]*)\]', output):
        axioms.update(x.strip() for x in group.split(',') if x.strip())
    assert axioms <= {'propext', 'Quot.sound'}
    (HERE/'audit.txt').write_text(output)
    assert before == {str(p.relative_to(ROOT)): sha(p) for p in inputs}, 'Inputs changed during check'
    receipt = dict(
        status='SELECTED_DESIGN_FINITE_MODEL_PASS', selection='SELECTED_DESIGN',
        runtimeImplementationChanged=False, kotlinImplementationStarted=False,
        productionVerifiedByKernel=False, kotlinAdapterEquivalenceProved=False,
        fullAPAlgebraVerified=False, actualGcReclamationProved=False,
        projectQualityOrSpeedupMeasured=False, cpuBoundForReferenceInternerProved=False,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), toolchain=TOOLCHAIN,
        leanVersion=version, leanMaxMemoryMiB=768, leanThreads=1, cpuAffinityCount=1,
        moduleCount=1, theoremCount=theorem_count, auditedPublicDeclarationCount=len(declarations),
        declarations=declarations, axioms=sorted(axioms), noChoiceOrUnprovedAxioms=True,
        allExplicitPublicDefinitionsAndTheoremsAudited=True, inputsStable=True,
        inputHashes=before, baselineRevision=pins['baselineRevision'], referenceSourceRole=pins['sourceRole'],
        portableAudit=dict(path=str((HERE/'audit.txt').relative_to(ROOT)), sha256=sha(HERE/'audit.txt')),
        logs={str((work/name).relative_to(ROOT)): sha(work/name)
              for name in ['PackedStaticGuidance.log','Audit.lean','Audit.log']},
        limits=[
            'Input rows come from the existing normalization/domain/owner adapter; the AP algebra is not kernel verified.',
            'Ordered query equality uses the same candidate ordinal plan. Native index migration must preserve that exact plan and full callback arguments.',
            'All finite composition prefixes are equal for the unchanged deterministic transition/oracle; this is not whole-driver convergence or an AP proof.',
            'The cost model counts metadata, row headers and primitive references, not exact JVM bytes or actual GC reclamation.',
            'The executable finite reference interner is linear. No claim about its CPU complexity or Kotlin hash performance is made.',
            'No Kotlin edit, Gradle, analyzer, JFR, MAT or project experiment is performed by this checker.'
        ])
    (HERE/'checks.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['status','moduleCount','theoremCount',
          'auditedPublicDeclarationCount','axioms','inputsStable','kotlinImplementationStarted']}))


if __name__ == '__main__':
    main()
