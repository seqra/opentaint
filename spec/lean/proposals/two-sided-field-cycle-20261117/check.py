#!/usr/bin/env python3
"""Check the nested field recurrence, certificate and fresh cold searches."""
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
    assert parent['status'] == 'PASS' and parent['auditedDeclarations'] == 7468
    assert len(parent['models']) == 445
    for module, info in parent['models'].items():
        assert hashlib.sha256(Path(info['source']).read_bytes()).hexdigest() == info['sha256'], module
        for suffix in ('.lean', '.olean', '.txt'):
            source = args.dependencies / (module + suffix)
            if source.exists() and source.resolve() != (out / source.name).resolve():
                shutil.copy2(source, out / source.name)
    env = {**os.environ, 'ELAN_TOOLCHAIN': 'leanprover/lean4:v4.35.0', 'LEAN_PATH': str(out)}
    models = dict(parent['models'])
    total = 0
    for module, namespace in [('PairedContext','PairedContext'), ('TwoSidedSearch','TwoSidedSearch'), ('LaneProof','NestedFieldLane')]:
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
    checked = subprocess.run(['lean', '--run', 'TwoSidedSearch.lean'], cwd=out,
                             env=env, text=True, capture_output=True)
    log = checked.stdout + checked.stderr
    (out / 'SearchResults.txt').write_text(log)
    assert checked.returncode == 0 and 'warning:' not in log, log
    assert 'TWO_SIDED_CERTIFICATES total=882 disagreements=0' in log, log
    assert 'TWO_SIDED_SEARCH total=72 latestNatural=11 unfinished=0 noRouteWithNormal=0 possibleWithoutNormal=0' in log, log
    for name, trace_args, expected in [
        ('Before', ['trace'], 'TWO_SIDED_TRACE (0, (false, (true, [1, 3, 5])))'),
        ('After', ['trace', 'repair'], 'TWO_SIDED_TRACE (5, (false, (true, [1])))'),
    ]:
        trace = subprocess.run(['lean', '--run', 'TwoSidedSearch.lean', *trace_args],
                               cwd=out, env=env, text=True, capture_output=True)
        (out / (name + 'Trace.txt')).write_text(trace.stdout + trace.stderr)
        assert trace.returncode == 0 and expected in trace.stdout, trace
    receipt = dict(status='PASS', leanVersion=parent['leanVersion'], models=models,
                   newDeclarations=total, auditedDeclarations=sum(v['auditedDeclarations'] for v in models.values()),
                   parentReceipt=str(args.dependencies / 'receipt.json'),
                   parentReceiptSha256=hashlib.sha256((args.dependencies / 'receipt.json').read_bytes()).hexdigest(),
                   rule='R40 [REC]: one nested side against a regular field language',
                   baselineRevision='966a40c3647268cc006e5776591d6b68849379d0',
                   search=dict(certificateCases=882, coldCases=72, latestNaturalRun=11, summary=log.strip()),
                   productionChanged=False, extraFieldCapExceptions=False,
                   wholeAnalyzerNoFalseNegativeProof=False, wholeAnalyzerTerminationProof=False)
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(newDeclarations=total, auditedDeclarations=receipt['auditedDeclarations'],
                          modules=len(models), search=log.strip()), indent=2))


if __name__ == '__main__':
    main()
