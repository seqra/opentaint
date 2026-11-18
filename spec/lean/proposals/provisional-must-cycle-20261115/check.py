#!/usr/bin/env python3
"""Compile and audit the constructive uncapped MUST replay cycle externally."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    refs = package.parent / 'non-empty-may-20261113'
    sources = [refs / (name + '.lean') for name in ('NonEmptyMay', 'Policy', 'Restriction')]
    sources += [package.parent / 'constant-filter-target-zero-20261031' / 'TargetZeroKernel.lean',
                package / 'Cycle.lean']
    models = {}
    for source in sources:
        contents = source.read_text()
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b', contents, re.M), source
        shutil.copy2(source, out / source.name)
        run = subprocess.run(['lean', '-o', source.stem + '.olean', source.name], cwd=out,
                             env={**os.environ, 'LEAN_PATH': str(out)}, capture_output=True, text=True)
        log = run.stdout + run.stderr
        (out / (source.stem + '.txt')).write_text(log)
        if run.returncode:
            print(log)
            raise SystemExit(run.returncode)
        models[source.stem] = dict(source=str(source), sha256=hashlib.sha256(source.read_bytes()).hexdigest())
    claims = re.findall(r'^theorem (\w+)', (package / 'Cycle.lean').read_text(), re.M)
    audit = 'import Cycle\n' + ''.join('#print axioms ProvisionalMustCycle.' + name + '\n' for name in claims)
    (out / 'Audit.lean').write_text(audit)
    run = subprocess.run(['lean', 'Audit.lean'], cwd=out, env={**os.environ, 'LEAN_PATH': str(out)}, capture_output=True, text=True)
    log = run.stdout + run.stderr
    (out / 'Audit.txt').write_text(log)
    assert run.returncode == 0, log
    audited = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log)
    assert len(audited) == len(claims), (len(audited), len(claims))
    for name, axioms in audited:
        assert set(axioms.replace('\n', '').split(', ')) - {''} <= {'propext', 'Quot.sound'}, (name, axioms)
    receipt = dict(status='PASS', newDeclarations=len(audited), models=models,
        leanVersion=subprocess.check_output(['lean', '--version'], text=True).strip(),
        scope='Concrete conditional T-to-U producer, direct native MUST provisional replay, complete cold six-run prefix and uncapped ZERO/Target recurrence; no loops/recursion/cleaners/pass rules; not a whole-analyzer simulation.')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(dict(status='PASS', declarations=len(audited), modules=len(models), receipt=str(out/'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
