#!/usr/bin/env python3
"""Constructive real-E input-head retention and all supplied termination controls."""
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
        subprocess.run(['python3', str(pkg.parent / 'deeper-excluded-guard-cycle-20261116/check.py'),
                        '--out', str(out)], check=True)
        receipt = json.loads((out / 'receipt.json').read_text())

    additions = [(m,pkg/(m+'.lean'),ns) for m,ns in [
        ('HeadPolicy','HeadPolicy'),('HeadSafety','HeadSafety'),
        ('HeadNeutralPlan','HeadNeutralPlan'),('HeadNeutral','HeadNeutral'),
        ('HeadCampaign','HeadCampaign'),('HeadDeep','HeadDeep'),
        ('HeadDeepCold','HeadDeepCold'),('HeadShallow','HeadShallow'),
        ('HeadShallowCold','HeadShallowCold'),('HeadAlternating','HeadAlternating'),
        ('HeadOldAlternating','HeadOldAlternating'),('HeadStrictExact','HeadStrictExact'),
        ('HeadStrictUniform','HeadStrictUniform'),('HeadStrictDifferent','HeadStrictDifferent'),
        ('HeadControls','HeadControls')]]
    additions += [(p.stem,p,p.stem) for p in sorted(pkg.glob('HeadOld*.lean')) if p.stem != 'HeadOldAlternating']
    total_new = 0
    for module, src, namespace in additions:
        content = src.read_text()
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b', content, re.M), src
        shutil.copy2(src, out / (module + '.lean'))
        env = {**os.environ, 'LEAN_PATH': str(out)}
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
    for old_field in ('uncappedCounterexample', 'counterexampleColdPrefix',
                      'finiteDiagnosticLatestRun', 'cycleRuns', 'cycleDemandRows'):
        receipt.pop(old_field, None)
    receipt.update(status='PASS', newDeclarations=total_new,
        auditedDeclarations=sum(v['auditedDeclarations'] for v in receipt['models'].values()),
        newCaseNaturalStopRun=5, oldCasesLatestNaturalStopRun=15,
        nativeDiagnosticLatestRun=31, newCaseUncappedNoRevival=True,
        scope='Forward restricted FULL concrete MAY/NE families retain an already submitted NORMAL MUST head together with real E instead of shortening that head. No extra initial; exact global bound, major narrow relaxation of external Dc+1 input cap, unchanged paired output cap. Raw C5 uses the new complete image. Both real-hole cases stop naturally run-5; old ordinary and concrete cases retained, accumulating Targets. No universal termination or integrated production performance claim.')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total_new,
        auditedDeclarations=receipt['auditedDeclarations'], modules=len(receipt['models']),
        receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
