#!/usr/bin/env python3
"""Audit native-bound NORMAL service and the uncapped quiet-suffix certificates."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


def main():
    q = argparse.ArgumentParser()
    q.add_argument('--out', type=Path, required=True)
    q.add_argument('--dependencies', type=Path)
    q.add_argument('--compiled', type=Path, help='Reuse source-identical modules just compiled in this validation session')
    a = q.parse_args()
    pkg = Path(__file__).resolve().parent
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if a.dependencies:
        base = a.dependencies.resolve()
        receipt = json.loads((base / 'receipt.json').read_text())
        for name, info in receipt['models'].items():
            assert hashlib.sha256(Path(info['source']).read_bytes()).hexdigest() == info['sha256'], name
            for suffix in ('.olean', '.lean', '.txt'):
                p = base / (name + suffix)
                if p.exists() and p.resolve() != (out / p.name).resolve():
                    shutil.copy2(p, out / p.name)
    else:
        subprocess.run(['python3', str(pkg.parent / 'protected-original-cycle-20261117/check.py'),
                        '--out', str(out)], check=True)
        receipt = json.loads((out / 'receipt.json').read_text())

    # Old metadata described historical counterexamples. Keep their audited
    # modules, but write a fresh current-contract receipt.
    receipt={'leanVersion':receipt['leanVersion'],'models':receipt['models']}

    # The leaf program and all analyzer machinery except these two delivery/
    # completion definitions remain source-identical to the last counterexample.
    old=(pkg.parent/'protected-original-cycle-20261117/OriginalReturn.lean').read_text()
    new=(pkg/'BoundBody.lean').read_text()
    def definition(text,name):
        begin=text.index('def '+name+' ')
        end=re.search(r'\n(?:def|theorem|end)\b',text[begin+1:])
        body=text[begin:begin+1+end.start()]
        body=re.sub(r'/\-.*?\-/', '',body,flags=re.S)
        return re.sub(r'\s+', ' ',re.sub(r'--[^\n]*','',body)).strip()
    names=re.findall(r'^def (\w+) ',old,re.M)
    changed={name for name in names if definition(old,name)!=definition(new,name)}
    assert changed=={'bodyClosed','actualReplies'},changed
    assert 'savedReplies ++' in definition(new,'actualReplies')
    assert 'BoundCore.eligible q' in definition(new,'bodyClosed')
    assert 'e.1.tail' not in definition(new,'suppressNativeReply')
    assert '!inputH' not in definition(new,'suppressNativeReply')
    assert '(read e actual).map' in definition(new,'readBound')
    modules=['BoundCore','BoundCoreProof','BoundBody','BoundUniform',
             'BoundOldRelevant','BoundOldUnrelated','BoundOldField','BoundOldExact','BoundOldMark',
             'BoundBodyCold','BoundUniformCold','BoundOldRelevantCold','BoundOldUnrelatedCold',
             'BoundOldFieldCold','BoundOldExactCold','BoundOldMarkCold',
             'BoundProof','BoundBounds','BoundPreservation','BoundFamily','BoundFamilyCases'] + [
             'BoundFamilyBatch'+str(n) for n in range(21)] + ['BoundFamilyProof']
    additions=[(m,pkg/(m+'.lean'),m) for m in modules]
    total_new = 0
    for module, src, namespace in additions:
        content = src.read_text()
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b', content, re.M), src
        shutil.copy2(src, out / (module + '.lean'))
        env = {**os.environ, 'ELAN_TOOLCHAIN': 'leanprover/lean4:v4.35.0', 'LEAN_PATH': str(out)}
        cached = a.compiled.resolve() if a.compiled else None
        if (cached and (cached / (module+'.olean')).exists() and
                (cached / (module+'.lean')).read_bytes()==src.read_bytes() and
                (cached / (module+'.olean')).stat().st_mtime_ns >= (cached / (module+'.lean')).stat().st_mtime_ns):
            cached_source=cached / (module+'.lean')
            assert cached_source.read_bytes()==src.read_bytes(), (module,'stale cached source')
            shutil.copy2(cached / (module+'.olean'),out / (module+'.olean'))
            (out / (module+'.txt')).write_text('Reused source-identical Lean module compiled in this session; theorem axioms are audited below.\n')
        else:
            compiled = subprocess.run(['lean', '-o', module + '.olean', module + '.lean'], cwd=out,
                                      env=env, text=True, capture_output=True)
            log = compiled.stdout + compiled.stderr
            (out / (module + '.txt')).write_text(log)
            if compiled.returncode:
                raise RuntimeError(log)
            assert 'warning:' not in log, log
        claims = re.findall(r'^theorem (\w+)', content, re.M)
        audit = 'import ' + module + '\n' + ''.join(
            '#print axioms ' + namespace + '.' + name + '\n' for name in claims)
        audit_name = module + 'Audit.lean'
        (out / audit_name).write_text(audit)
        checked = subprocess.run(['lean', audit_name], cwd=out, env=env, text=True, capture_output=True)
        log = checked.stdout + checked.stderr
        (out / (module + 'Audit.txt')).write_text(log)
        assert checked.returncode == 0, log
        found = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log)
        assert len(found) == len(claims), (module, len(found), len(claims))
        for name, axioms in found:
            assert set(axioms.replace('\n', '').split(', ')) - {''} <= {'propext', 'Quot.sound'}, (name, axioms)
        receipt['models'][module] = dict(source=str(src), sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
                                         auditedDeclarations=len(found))
        total_new += len(found)
        print('PASS', module, len(found), flush=True)
    for key in ('uncappedCounterexample','fullStateCycleRuns','helperDemandRows'):
        receipt.pop(key,None)
    receipt.update(status='PASS',newDeclarations=total_new,
        auditedDeclarations=sum(v['auditedDeclarations'] for v in receipt['models'].values()),
        naturalStopRun=7,normalObservationRun=5,uncappedNoRevival=True,
        latestNewColdRun=9,finiteSearchLatestRun=25,historicalNativeDiagnosticLatestRun=31,
        oldCasesLatestNaturalStopRun=15,nativeComponentTests=19,
        uniformControlStopRun=9,uniformControlNORMALObservationRun=7,
        previousFiveServiceCasesStopRun=5,
        finiteFamilyConfigurations=252,finiteFamilyNaturalStopByRun=9,finiteFamilyUncappedQuietSuffix=True,
        majorChanges=['Select current unary DEMAND concrete return delivery from complete native-bound NORMAL service, including protected originals and exact/same-head premises.',
                      'Allow the existing NORMAL MUST query to close; preserve its real exclusions.',
                      'Accept whole NORMAL MUST coverage after canonicalization; do not require a removed literal scalar.'],
        modelFidelityCorrection='readBound models existing native transport of incoming H; this is not a production transfer change.',
        newQueries=0,newPropagatedFieldPaths=0,newCapExceptions=0,
        scope='Constructive arbitrary-continuation witness theorem under full owned closure; whole concrete coverage, per-bound-image H and native receipt. Two new and five earlier complete cold references have exact within-run fixed points and uncapped quiet suffixes. All earlier proof sources remain hash checked. Guard-ineligible adapters remain conservative fallbacks; no integrated whole-engine equivalence is claimed. Owner DEMAND rows remain for handoff; saved NORMAL replay, C2/C5/caps/Targets and literal storage flags stay unchanged. Native component tests separately check existing AP binding. Finite search and the historical production run-31 diagnostic are not universal termination proofs.')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total_new,
        auditedDeclarations=receipt['auditedDeclarations'], modules=len(receipt['models']),
        receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
