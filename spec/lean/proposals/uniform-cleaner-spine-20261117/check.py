#!/usr/bin/env python3
"""Recheck R35/R36, the uncapped counterexamples and the finite cleaner search."""
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
    parser.add_argument('--dependencies', type=Path, required=True,
                        help='Source-hash-checked post-DIRECT proof receipt and compiled modules')
    args = parser.parse_args()
    pkg = Path(__file__).resolve().parent
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    parent = json.loads((args.dependencies / 'receipt.json').read_text())
    assert parent['status'] == 'PASS' and parent['auditedDeclarations'] == 7245
    assert len(parent['models']) == 422
    for module, info in parent['models'].items():
        assert hashlib.sha256(Path(info['source']).read_bytes()).hexdigest() == info['sha256'], module
        for suffix in ('.olean', '.lean', '.txt'):
            source = args.dependencies / (module + suffix)
            if source.exists() and source.resolve() != (out / source.name).resolve():
                shutil.copy2(source, out / source.name)
    env = {**os.environ, 'ELAN_TOOLCHAIN': 'leanprover/lean4:v4.35.0', 'LEAN_PATH': str(out)}
    models = dict(parent['models'])
    modules = [(pkg.parent / 'descendant-cleaner-cycle-20261117', 'DescendantCleanerCycle'),
               (pkg.parent / 'descendant-cleaner-cycle-20261117', 'ExactMUSTClosure'),
               (pkg, 'UniformCleanerSpine'), (pkg, 'NestedCleanerProtocol'), (pkg, 'CleanerSearch')]
    total = 0
    for folder, module in modules:
        source = folder / (module + '.lean')
        content = source.read_text()
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b', content, re.M)
        shutil.copy2(source, out / source.name)
        checked = subprocess.run(['lean', '-o', module + '.olean', source.name], cwd=out,
                                 env=env, text=True, capture_output=True)
        log = checked.stdout + checked.stderr
        (out / (module + '.txt')).write_text(log)
        assert checked.returncode == 0 and 'warning:' not in log, log
        claims = re.findall(r'^theorem (\w+)', content, re.M)
        audit = 'import ' + module + '\n' + ''.join(
            '#print axioms ' + module + '.' + claim + '\n' for claim in claims)
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
        models[module] = dict(source=str(source), sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                              auditedDeclarations=len(found))
        total += len(found)
        print('PASS', module, len(found), flush=True)
    (out / 'RunSearch.lean').write_text('import CleanerSearch\n#eval CleanerSearch.main\n')
    checked = subprocess.run(['lean', 'RunSearch.lean'], cwd=out, env=env, text=True, capture_output=True)
    log = checked.stdout + checked.stderr
    (out / 'CleanerSearchResults.txt').write_text(log)
    assert checked.returncode == 0 and 'warning:' not in log and 'GAP' not in log and 'EARLY' not in log, log
    assert 'pipelines=56700 cases=2551500 failures=0 latestNaturalRun=5 maxRows=7' in log, log
    receipt = dict(status='PASS', leanVersion=parent['leanVersion'], models=models,
                   newDeclarations=total, auditedDeclarations=sum(v['auditedDeclarations'] for v in models.values()),
                   parentReceipt=str(args.dependencies / 'receipt.json'),
                   parentReceiptSha256=hashlib.sha256((args.dependencies / 'receipt.json').read_bytes()).hexdigest(),
                   newSemanticRules=['R35: projection-closed selected EXACT/MUST policy',
                                     'R36: path-linear NORMAL MUST subtree residual after run-1'],
                   selectedExactPointCoarsening=True, extraFieldCapExceptions=False,
                   productionChanged=False, uncappedRecurrenceProofs=True,
                   referenceLatestNaturalRuns=[1, 3], currentNativeDiagnosticRun=15,
                   search=dict(pipelines=56700, cases=2551500, latestNaturalRun=5,
                               result=log.strip(), source=str(pkg / 'CleanerSearch.lean'),
                               scope='Single local; source EXACT/MUST paths<=2; optional source E components; two cleaners paths<=3; EXACT/ALL/BELOW; observations EXACT/MAY/NE paths<=3. Main ZERO/Target admission and backward source permission. No call/ND/alias/static/group completeness claim.'),
                   wholeAnalyzerNoFalseNegativeProof=False, wholeAnalyzerTerminationProof=False)
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total, auditedDeclarations=receipt['auditedDeclarations'],
                          modules=len(models), search=log.strip(), receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
