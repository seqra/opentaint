#!/usr/bin/env python3
"""Constructive complete-point NORMAL service repair; no new queries or field-cap exception."""
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
        subprocess.run(['python3', str(pkg.parent / 'exact-input-guard-cycle-20261116/check.py'),
                        '--out', str(out)], check=True)
        receipt = json.loads((out / 'receipt.json').read_text())

    # Old transfer/admission/publication bodies remain unchanged apart from comments.
    old = (pkg.parent / 'exact-input-guard-cycle-20261116/ExactGuard.lean').read_text()
    new = (pkg / 'CompletePoint.lean').read_text()
    def definition(text, name):
        begin = text.index('def ' + name + ' ')
        match = re.search(r'\n(?:def|theorem|end)\b', text[begin + 1:])
        body = text[begin:begin + 1 + match.start()]
        body = re.sub(r'/\-.*?\-/', '', body, flags=re.S)
        return re.sub(r'\s+', ' ', re.sub(r'--[^\n]*', '', body)).strip()
    for name in ('gen','read','prepare','candidates','firstFields','reverseGen','outputRows'):
        assert definition(old,name) == definition(new,name), name
    additions = [(m,pkg/(m+'.lean'),m) for m in (
        'CompleteClosure','CompletePoint','CompleteService','CompleteCold',
        'LateCompletePoint','LateCompleteCold','CompleteBounds','CompleteRegression')]
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
    for historical in ('uncappedCounterexample','cycleRuns','cycleDemandRows',
                       'counterexampleColdPrefix','historicalCounterexampleCycleRuns'):
        receipt.pop(historical,None)
    receipt.update(status='PASS', newDeclarations=total_new,
        auditedDeclarations=sum(v['auditedDeclarations'] for v in receipt['models'].values()),
        newCaseNaturalStopRun=5, delayedCertificateNaturalStopRun=7,
        newCaseUncappedNoRevival=True, newCaseNormalObservationRun=3,
        newCaseCompletionKeys=3, newInputCapExceptions=0, newQueries=0,
        priorLargestNaturalStopRun=15, finiteDiagnosticLatestRun=31,
        scope='Executable finite NORMAL-closure certificate and return-service preservation. Exact-input/Empty-E counterexample full cold trace, fixed points and uncapped quiet suffix, including late-certificate scheduling with accumulating Targets. Eighteen old multi-owner field-flow references and three older conditional histories have no eligible deletion at any event subset; strict MUST inputs and protected effects remain excluded. Previous hashed proof packages retained. No production policy is implemented, no whole-engine equivalence, no universal termination or project-performance claim.')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total_new,
        auditedDeclarations=receipt['auditedDeclarations'], modules=len(receipt['models']),
        receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
