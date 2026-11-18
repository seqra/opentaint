#!/usr/bin/env python3
"""Constructive mark-scoped NORMAL return completion; no new paths or queries."""
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
        subprocess.run(['python3', str(pkg.parent / 'unadmitted-return-cycle-20261116/check.py'),
                        '--out', str(out)], check=True)
        receipt = json.loads((out / 'receipt.json').read_text())

    # The program and all admission/transfer/restriction functions stay unchanged.
    old=(pkg.parent/'unadmitted-return-cycle-20261116/UnadmittedReturn.lean').read_text()
    new=(pkg/'ScopedBody.lean').read_text()
    def definition(text,name):
        begin=text.index('def '+name+' ')
        end=re.search(r'\n(?:def|theorem|end)\b',text[begin+1:])
        body=text[begin:begin+1+end.start()]
        body=re.sub(r'/\-.*?\-/', '',body,flags=re.S)
        return re.sub(r'\s+', ' ',re.sub(r'--[^\n]*','',body)).strip()
    for name in ('gen','entryValues','reverseGen','read','firstFields','prepare','candidates','queries',
                 'completePoint','certify','suppress','delivered','normalizeContinuation',
                 'outputRows','outputSaved','producerHit'):
        assert definition(old,name)==definition(new,name),name
    additions=[(m,pkg/(m+'.lean'),m) for m in (
        'ScopedCore','ScopedBody','LateScopedBody','ScopedCold','LateScopedCold',
        'ScopedHomogeneous','ScopedProof','ScopedBounds','ScopedRegression')]
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
    for key in ('uncappedCounterexample','cycleRuns','cycleDemandRows','coldPrefix','sourceProgram'):
        receipt.pop(key,None)
    receipt.update(status='PASS',newDeclarations=total_new,
        auditedDeclarations=sum(v['auditedDeclarations'] for v in receipt['models'].values()),
        naturalStopRun=5,delayedReceiptNaturalStopRun=7,uncappedNoRevival=True,
        normalObservationRun=3,wholeCompletionKeys=1,additionalMarkScopedKeys=2,
        newInitials=0,newFieldPaths=0,newCapExceptions=0,
        priorLargestNaturalStopRun=15,finiteNativeDiagnosticLatestRun=31,
        scope='Shared full NORMAL closure; projected terminal output-mark coverage and native delivery receipt. Exact unchanged six-rule counterexample cold states/fixed points/natural run-5 stop and uncapped quiet suffix; delayed receipt run-7 stop with accumulating Target. Sparse grouping equivalent to reference predicate. Old homogeneous marked bodies add no scoped cells for any query/store; abstract/strict inputs and protection retain their gates. No production implementation, no whole-engine/JVM/alias equivalence, no universal termination or project-performance theorem.')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total_new,
        auditedDeclarations=receipt['auditedDeclarations'], modules=len(receipt['models']),
        receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
