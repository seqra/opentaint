#!/usr/bin/env python3
"""Uncapped same-mark disjoint-return counterexample; no policy repair."""
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
        subprocess.run(['python3', str(pkg.parent / 'mark-scoped-point-service-20261116/check.py'),
                        '--out', str(out)], check=True)
        receipt = json.loads((out / 'receipt.json').read_text())

    # Only the synthetic leaf program and the caller's ordinary h read differ.
    # Completion and every admission, intersection and reply gate remain enabled.
    old=(pkg.parent/'mark-scoped-point-service-20261116/ScopedBody.lean').read_text()
    new=(pkg/'FieldCycle.lean').read_text()
    def definition(text,name):
        begin=text.index('def '+name+' ')
        end=re.search(r'\n(?:def|theorem|end)\b',text[begin+1:])
        body=text[begin:begin+1+end.start()]
        body=re.sub(r'/\-.*?\-/', '',body,flags=re.S)
        return re.sub(r'\s+', ' ',re.sub(r'--[^\n]*','',body)).strip()
    for name in ('originalSource','entryValues','read','firstFields','prepare','queries',
                 'completePoint','certify','certifyMarks','suppress','suppressMark',
                 'delivered','deliveredMark','actualReplies','normalizeContinuation',
                 'publishAt','outputRows','outputSaved','producerHit','anyTarget','stepWithLimit'):
        assert definition(old,name)==definition(new,name),name
    additions=[(m,pkg/(m+'.lean'),m) for m in (
        'FieldCycle','FieldPhase','FieldFrozen','FieldCold','FieldRounds',
        'FieldSteady','FieldKernel','FieldRecurrence','FieldBounds')]
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
    for key in ('naturalStopRun','delayedReceiptNaturalStopRun','uncappedNoRevival',
                'normalObservationRun','wholeCompletionKeys','additionalMarkScopedKeys'):
        receipt.pop(key,None)
    receipt.update(status='PASS',newDeclarations=total_new,
        auditedDeclarations=sum(v['auditedDeclarations'] for v in receipt['models'].values()),
        uncappedCounterexample=True,fullStateCycleRuns=[11,12],cycleDemandRows=[70,82],
        sameHandoffFrontierFromRun=9,coldPrefix=10,finiteDiagnosticLatestRun=31,
        wholeCompletionEnabled=True,fullMarkScopedCompletionEnabled=True,
        steadyCompletionKeys=0,newFieldCapExceptions=0,newQueries=0,
        sourceProgram='Ordinary allocation, return and field read; three sequential acyclic calls; six positive unary marking rules; root exact marking and observation. No loop, recursion, cleaner, pass, unresolved or predefined relation.',
        scope='Current selected admission/C5/completion/reply functions source-identical to ScopedBody. All steady state, within-run fixed point, arbitrary later budget and uncapped recurrence claims kernel checked. Same output mark has both hh and disjoint k NORMAL raw effects; C5 drops k, so neither whole nor mark-scoped completion is proved. Plain H; Empty E/mx; all global and Dc+1 input caps and paired Dp+1 output caps retained; accumulated Targets remain. Native finite run-31/POLICY has zero NORMAL reports; scalar reference has a NORMAL observation from run-5. No integrated NE/proposal implementation or whole-engine/JVM/alias equivalence is claimed. Production unchanged.')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total_new,
        auditedDeclarations=receipt['auditedDeclarations'], modules=len(receipt['models']),
        receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
