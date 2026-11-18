#!/usr/bin/env python3
"""A protected exact caller input blocks the selected same-flag delivery certificate."""
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
        subprocess.run(['python3', str(pkg.parent / 'flag-aware-reply-service-20261117/check.py'),
                        '--out', str(out)], check=True)
        receipt = json.loads((out / 'receipt.json').read_text())

    # Only the analyzed program and observation mark change. Every analyzer
    # definition, including the latest layer-aware completion guards, stays identical.
    old=(pkg.parent/'flag-aware-reply-service-20261117/FlagBody.lean').read_text()
    new=(pkg/'OriginalReturn.lean').read_text()
    def definition(text,name):
        begin=text.index('def '+name+' ')
        end=re.search(r'\n(?:def|theorem|end)\b',text[begin+1:])
        body=text[begin:begin+1+end.start()]
        body=re.sub(r'/\-.*?\-/', '',body,flags=re.S)
        return re.sub(r'\s+', ' ',re.sub(r'--[^\n]*','',body)).strip()
    names=re.findall(r'^def (\w+) ',old,re.M)
    allowed={'gen','reverseGen'}
    changed={name for name in names if name!='kfield' and definition(old,name)!=definition(new,name)}
    assert changed==allowed,changed
    assert definition(new,'colors')=='def colors : List Color := [.t]'
    assert '!originalH' in definition(new,'suppressFlaggedReply')
    assert 'LayerCore.normalLayer c' in definition(new,'bodyClosed')
    assert 'LayerCore.completeFor' in definition(new,'suppressReply')
    additions=[(m,pkg/(m+'.lean'),m) for m in (
        'OriginalReturn','OriginalPhase','OriginalFrozen','OriginalCold',
        'OriginalRounds','OriginalSteady','OriginalKernel','OriginalRecurrence','OriginalBounds')]
    total_new = 0
    for module, src, namespace in additions:
        content = src.read_text()
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b', content, re.M), src
        shutil.copy2(src, out / (module + '.lean'))
        env = {**os.environ, 'ELAN_TOOLCHAIN': 'leanprover/lean4:v4.35.0', 'LEAN_PATH': str(out)}
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
    for key in ('naturalStopRun','uncappedNoRevival','normalObservationRun',
                'currentOnlyClosureKeysAtRun3','currentOnlyClosureKeysAtRun5'):
        receipt.pop(key,None)
    receipt.update(status='PASS',newDeclarations=total_new,
        auditedDeclarations=sum(v['auditedDeclarations'] for v in receipt['models'].values()),
        uncappedCounterexample=True,fullStateCycleRuns=[9,10],helperDemandRows=[39,45],
        sourceProgram='Ordinary allocation, return and h reads; three acyclic calls; two positive same-mark assignments to fresh h.MUST and h.f.g.EXACT result fields. The second and third exact inputs are protected. One mark T. No loops, recursion, cleaners, special pass or unresolved models.',
        layerAwareCompletionEnabled=True,fullMarkCompletionEnabled=True,replyScopedCompletionEnabled=True,
        fullNormalClosureReadyAtSteadyForward=True,currentClosureKeys=1,
        newQueries=0,newPropagatedFieldPaths=0,newCapExceptions=0,
        finiteNativeDiagnosticLatestRun=31,
        scope='Counterexample to the selected within-flag reply-service approach. Only the analyzed source actions and their reversal change; every analyzer function, including original-H fallback, is source-identical. The first plain original can use complete NORMAL service, but subsequent protected exact originals cannot. Full NORMAL closure and whole same-flag native service are ready. Kernel-checked cold transitions, within-run fixed points, arbitrary-limit stages and exact uncapped run-9/run-10 recurrence retain 39/45 rows and one NORMAL record. All caps, literal H and Targets are unchanged. Native finite run-31/POLICY is only an unchanged production diagnostic, not proposal integration or an uncapped proof. No repair is selected here.')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total_new,
        auditedDeclarations=receipt['auditedDeclarations'], modules=len(receipt['models']),
        receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
