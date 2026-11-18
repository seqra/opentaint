#!/usr/bin/env python3
"""Constructive normal uniform actual DATA coverage and termination references."""
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
    q.add_argument('--reuse-checked', action='store_true')
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
        subprocess.run(['python3', str(pkg.parent / 'alternating-condition-cycle-20261116/check.py'),
                        '--out', str(out)], check=True)
        receipt = json.loads((out / 'receipt.json').read_text())

    additions = [('UniformActual', pkg / 'UniformActual.lean', 'UniformActual'),
                 ('UniformSafety', pkg / 'UniformSafety.lean', 'UniformSafety'),
                 ('UniformProtected', pkg / 'UniformProtected.lean', 'UniformProtected'),
                 ('UniformReplay', pkg / 'UniformReplay.lean', 'UniformReplay'),
                 ('UniformCampaign', pkg / 'UniformCampaign.lean', 'UniformCampaign'),
                 ('UniformAlternating', pkg / 'UniformAlternating.lean', 'UniformAlternating'),
                 ('UniformSticky', pkg / 'UniformSticky.lean', 'UniformSticky'),
                 ('UniformStrictExact', pkg / 'UniformStrictExact.lean', 'UniformStrictExact'),
                 ('UniformStrictUniform', pkg / 'UniformStrictUniform.lean', 'UniformStrictUniform'),
                 ('UniformStrictDifferent', pkg / 'UniformStrictDifferent.lean', 'UniformStrictDifferent')]
    additions += [(p.stem, p, p.stem) for p in sorted(pkg.glob('UniformCold*.lean'))]
    additions += [(p.stem, p, p.stem) for p in sorted(pkg.glob('UniformStickyCold*.lean'))]
    total_new = 0
    for module, src, namespace in additions:
        content = src.read_text()
        known = receipt['models'].get(module)
        if a.reuse_checked and known and hashlib.sha256(src.read_bytes()).hexdigest() == known['sha256'] and (out / (module + '.olean')).exists():
            total_new += known['auditedDeclarations']
            print('REUSE', module, known['auditedDeclarations'], flush=True)
            continue
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b', content, re.M), src
        shutil.copy2(src, out / (module + '.lean'))
        env = {**os.environ, 'LEAN_PATH': str(out)}
        compiled = subprocess.run(['lean', '-o', module + '.olean', module + '.lean'], cwd=out,
                                  env=env, text=True, capture_output=True)
        log = compiled.stdout + compiled.stderr
        (out / (module + '.txt')).write_text(log)
        if compiled.returncode:
            raise RuntimeError(log[:6000])
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
    receipt.update(status='PASS', newDeclarations=total_new,
        auditedDeclarations=sum(v['auditedDeclarations'] for v in receipt['models'].values()),
        latestColdRun=15, newCaseColdRun=5,
        selectedTargetSemantics='Accumulate every reached Target; late DATA coverage does not undo effects.',
        scope='Forward FULL actual NORMAL uniform DATA covers an entire MAY/NE demand region at the same actual continuation, with real E and literal protection. This filters existing packets without new facts or queries. No production integration or universal termination theorem.')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total_new,
        auditedDeclarations=receipt['auditedDeclarations'], modules=len(receipt['models']),
        receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
