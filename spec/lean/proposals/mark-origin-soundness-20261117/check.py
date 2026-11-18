#!/usr/bin/env python3
"""Compile the origin-specific loss, R38 certificate and fresh comparative search."""
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
    parser.add_argument('--dependencies', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    pkg = Path(__file__).resolve().parent
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    parent = json.loads((args.dependencies / 'receipt.json').read_text())
    assert parent['status'] == 'PASS' and parent['auditedDeclarations'] == 7360
    assert len(parent['models']) == 431
    for module, info in parent['models'].items():
        assert hashlib.sha256(Path(info['source']).read_bytes()).hexdigest() == info['sha256'], module
        for suffix in ('.lean', '.olean', '.txt'):
            source = args.dependencies / (module + suffix)
            if source.exists() and source.resolve() != (out / source.name).resolve():
                shutil.copy2(source, out / source.name)
    env = {**os.environ, 'ELAN_TOOLCHAIN': 'leanprover/lean4:v4.35.0', 'LEAN_PATH': str(out)}
    models = dict(parent['models'])
    total = 0
    for module, namespace in [(m,m) for m in ['LostMarkOrigin', 'OriginService', 'OriginGrowth', 'OriginRepair', 'OriginSearch']]:
        source = pkg / (module + '.lean')
        content = source.read_text()
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b', content, re.M)
        shutil.copy2(source, out / source.name)
        checked = subprocess.run(['lean', '-o', module + '.olean', source.name], cwd=out,
                                 env=env, text=True, capture_output=True)
        log = checked.stdout + checked.stderr
        (out / (module + '.txt')).write_text(log)
        assert checked.returncode == 0 and 'warning:' not in log, log
        claims = re.findall(r'^theorem (\w+)', content, re.M)
        name = module + 'Audit.lean'
        (out / name).write_text('import ' + module + '\n' + ''.join(
            '#print axioms ' + namespace + '.' + claim + '\n' for claim in claims))
        checked = subprocess.run(['lean', name], cwd=out, env=env, text=True, capture_output=True)
        log = checked.stdout + checked.stderr
        (out / (module + 'Audit.txt')).write_text(log)
        assert checked.returncode == 0, log
        found = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log)
        assert len(found) == len(claims), (module, len(found), len(claims))
        for name, axioms in found:
            assert set(axioms.replace('\n', '').split(', ')) - {''} <= {'propext', 'Quot.sound'}, (name, axioms)
        models[module] = dict(source=str(source), sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                              auditedDeclarations=len(found))
        total += len(found)
        print('PASS', module, len(found), flush=True)
    (out / 'RunOriginSearch.lean').write_text('import OriginSearch\n#eval OriginSearch.main\n')
    checked = subprocess.run(['lean', 'RunOriginSearch.lean'], cwd=out, env=env, text=True, capture_output=True)
    log = checked.stdout + checked.stderr
    (out / 'OriginSearchResults.txt').write_text(log)
    assert checked.returncode == 0 and 'warning:' not in log and 'GAP' not in log and 'EARLY' not in log, log
    assert 'ORIGINS flat=6615 loops=735 recursive=336 failed=0 latestNaturalRun=9' in log, log
    receipt = dict(status='PASS', leanVersion=parent['leanVersion'], models=models,
                   newDeclarations=total, auditedDeclarations=sum(v['auditedDeclarations'] for v in models.values()),
                   parentReceipt=str(args.dependencies / 'receipt.json'),
                   parentReceiptSha256=hashlib.sha256((args.dependencies / 'receipt.json').read_bytes()).hexdigest(),
                   newRule='R38 [REC] [LOOP]: source-specific NORMAL service before root Target retirement',
                   productionChanged=False, extraFieldCapExceptions=False,
                   flatBaselineNaturalRun=5, flatR37LossNaturalRun=3, flatRepairNaturalRun=5,
                   loopNativeBaselineNaturalRun=13, loopNativeR37LossNaturalRun=5,
                   loopNativeRepairNaturalRun=13, twoSourceRecursiveNativeRepairRun=9,
                   search=dict(cases=7686, latestNaturalRun=9, summary=log.strip(),
                               scope='6615 flat single-move words with two marking points; 735 finite ordinary repeat-closure components with broad AL observation; 336 shared-state direct/mutual neutral wrappers with two original marking offers. Same full T, same observer ID. Source-specific NORMAL paths, not report counts. Hierarchical native loop controls separate at run13. No full ND/alias/static/GROUP/cleaner upper/lower adapter claim.'),
                   wholeAnalyzerNoFalseNegativeProof=False, wholeAnalyzerTerminationProof=False)
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total, auditedDeclarations=receipt['auditedDeclarations'],
                          modules=len(models), search=log.strip(), receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
