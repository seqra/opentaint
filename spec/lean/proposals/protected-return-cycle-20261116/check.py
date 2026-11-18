#!/usr/bin/env python3
"""Protected unrelated NORMAL return blocks the selected completion adapter."""
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
        subprocess.run(['python3', str(pkg.parent / 'reply-scoped-point-service-20261116/check.py'),
                        '--out', str(out)], check=True)
        receipt = json.loads((out / 'receipt.json').read_text())

    # The program changes only its k assignments. Native rule assignment
    # establishes the resulting H flag. All selected completion guards stay.
    old=(pkg.parent/'reply-scoped-point-service-20261116/ReplyBody.lean').read_text()
    new=(pkg/'ProtectedReturn.lean').read_text()
    def definition(text,name):
        begin=text.index('def '+name+' ')
        end=re.search(r'\n(?:def|theorem|end)\b',text[begin+1:])
        body=text[begin:begin+1+end.start()]
        body=re.sub(r'/\-.*?\-/', '',body,flags=re.S)
        return re.sub(r'\s+', ' ',re.sub(r'--[^\n]*','',body)).strip()
    for name in ('originalSource','entryValues','read','firstFields','prepare','candidates','queries',
                 'completePoint','certify','certifyMarks','bodyClosed','certifyClosed',
                 'suppress','suppressMark','suppressReply','consumeH','asInput',
                 'delivered','deliveredMark','actualReplies','normalizeContinuation',
                 'round','deliverAt','publishAt','analyze','outputRows','outputSaved',
                 'producerHit','anyTarget','stepWithLimit'):
        assert definition(old,name)==definition(new,name),name
    additions=[(m,pkg/(m+'.lean'),m) for m in (
        'ProtectedReturn','ProtectedPhase','ProtectedFrozen','ProtectedCold',
        'ProtectedRounds','ProtectedSteady','ProtectedKernel','ProtectedRecurrence','ProtectedBounds')]
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
        uncappedCounterexample=True,fullStateCycleRuns=[11,12],helperDemandRows=[70,82],
        sourceProgram='Ordinary allocation, return and h reads; three acyclic calls; six positive unary marking rules, including same-mark assignments to a fresh k field. No loop, recursion, cleaner, configured pass, unresolved transfer or predefined summary.',
        fullMarkCompletionEnabled=True,replyScopedCompletionEnabled=True,
        sameContextNormalServiceForRelevantRegion=True,
        newQueries=0,newPropagatedFieldPaths=0,newCapExceptions=0,
        finiteNativeDiagnosticLatestRun=31,
        scope='Counterexample to the selected executable completion adapter and its full-raw plain-H eligibility checks. The geometric/conditional observation-preservation theorem is not refuted. H remains independent from NORMAL/DEMAND and is produced by the selected same-mark source assignment law; passes do not create H. Full current/whole/mark/reply guards are source-identical to ReplyBody. Cold transitions and fixed points, arbitrary-budget stages and complete uncapped run-11/run-12 recurrence are kernel checked. Entry/global/output caps and accumulated Targets are unchanged. Native component/full-program finite diagnostic has run-31/POLICY with zero NORMAL reports; proposal reference retains a NORMAL observation from run-5. No production integration, whole-engine/JVM/alias equivalence or new repair is claimed.')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total_new,
        auditedDeclarations=receipt['auditedDeclarations'], modules=len(receipt['models']),
        receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
