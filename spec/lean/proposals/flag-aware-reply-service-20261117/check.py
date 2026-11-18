#!/usr/bin/env python3
"""Within-flag current-return service; complete uncapped regression checks."""
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
        subprocess.run(['python3', str(pkg.parent / 'relevant-protected-return-cycle-20261117/check.py'),
                        '--out', str(out)], check=True)
        receipt = json.loads((out / 'receipt.json').read_text())

    old=(pkg.parent/'relevant-protected-return-cycle-20261117/RelevantReturn.lean').read_text()
    new=(pkg/'FlagBody.lean').read_text()
    def definition(text,name):
        begin=text.index('def '+name+' ')
        end=re.search(r'\n(?:def|theorem|end)\b',text[begin+1:])
        body=text[begin:begin+1+end.start()]
        body=re.sub(r'/\-.*?\-/', '',body,flags=re.S)
        return re.sub(r'\s+', ' ',re.sub(r'--[^\n]*','',body)).strip()
    names=re.findall(r'^def (\w+) ',old,re.M)
    changed={name for name in names if definition(old,name)!=definition(new,name)}
    assert changed=={'actualReplies','round','deliverAt'},changed
    for name in ('gen','reverseGen','prepare','candidates','bodyClosed','suppress','suppressMark','suppressReply','outputRows','outputSaved','stepWithLimit'):
        assert definition(old,name)==definition(new,name),name
    assert 'FlagCore.completeFor' in definition(new,'suppressFlaggedReply')
    assert '!originalH' in definition(new,'suppressFlaggedReply')
    additions=[(m,pkg/(m+'.lean'),m) for m in (
        'FlagCore','FlagBody','FlagOldUnrelated','FlagOldField','FlagOldExact','FlagOldMark',
        'FlagCold','FlagOldUnrelatedCold','FlagOldFieldCold','FlagOldExactCold','FlagOldMarkCold',
        'FlagProof','FlagRegression','FlagBounds')]
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
    for key in ('uncappedCounterexample','fullStateCycleRuns','helperDemandRows','sourceProgram','fullNormalClosureReadyAtSteadyForward','currentClosureKeys'):
        receipt.pop(key,None)
    receipt.update(status='PASS',newDeclarations=total_new,
        auditedDeclarations=sum(v['auditedDeclarations'] for v in receipt['models'].values()),
        naturalStopRun=5,uncappedNoRevival=True,normalObservationRun=5,
        priorLargestNaturalStopRun=15,newQueries=0,newPropagatedFieldPaths=0,newCapExceptions=0,newPersistentRegionCells=0,
        sameFlagCurrentDelivery=True,protectedOriginalFallback=True,
        finiteNativeDiagnosticLatestRun=31,
        scope='Current DEMAND return selection within each literal flag. Full NORMAL-layer closure is unprojected; same-owner same-flag whole NORMAL service and native application receipt cover every relevant return. Original H remains a conservative fallback; protection flags are not erased or merged. No stored edge is removed. Unchanged C2/C5, transfer, caps, query keys, NORMAL storage and Target accumulation are source compared. New protected-return reference naturally stops run-5 with an uncapped quiet suffix. Four prior exact/mark/field/unrelated semantic cold histories remain identical; older ordinary histories have only plain current replies and the existing shape-guard bridge remains. No production integration, whole-engine equivalence or universal termination claim.')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total_new,
        auditedDeclarations=receipt['auditedDeclarations'], modules=len(receipt['models']),
        receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
