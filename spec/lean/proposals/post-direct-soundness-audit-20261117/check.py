#!/usr/bin/env python3
"""Check the post-DIRECT replay soundness investigation."""
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
    q.add_argument('--compiled', type=Path, help='Reuse source-identical modules just compiled in this validation session')
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
        subprocess.run(['python3', str(pkg.parent / 'saved-direct-possible-replay-20261117/check.py'),
                        '--out', str(out)], check=True)
        receipt = json.loads((out / 'receipt.json').read_text())

    # Old metadata described historical counterexamples. Keep their audited
    # modules, but write a fresh current-contract receipt.
    receipt={'leanVersion':receipt['leanVersion'],'models':receipt['models']}

    modules=['PostDirectReference','PostDirectChecks']
    additions=[(m,pkg/(m+'.lean'),m) for m in modules]
    total_new = 0
    for module, src, namespace in additions:
        content = src.read_text()
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b', content, re.M), src
        shutil.copy2(src, out / (module + '.lean'))
        env = {**os.environ, 'ELAN_TOOLCHAIN': 'leanprover/lean4:v4.35.0', 'LEAN_PATH': str(out)}
        cached = a.compiled.resolve() if a.compiled else None
        if (cached and (cached / (module+'.olean')).exists() and
                (cached / (module+'.lean')).read_bytes()==src.read_bytes() and
                (cached / (module+'.olean')).stat().st_mtime_ns >= (cached / (module+'.lean')).stat().st_mtime_ns):
            cached_source=cached / (module+'.lean')
            assert cached_source.read_bytes()==src.read_bytes(), (module,'stale cached source')
            shutil.copy2(cached / (module+'.olean'),out / (module+'.olean'))
            (out / (module+'.txt')).write_text('Reused source-identical Lean module compiled in this session; theorem axioms are audited below.\n')
        else:
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
    proposal=pkg.parents[3]/'docs/design/bidirectional-demand-termination-approach-20261115.md'
    receipt.update(status='PASS',newDeclarations=total_new,
        auditedDeclarations=sum(v['auditedDeclarations'] for v in receipt['models'].values()),
        proposalSource=str(proposal),proposalSha256=hashlib.sha256(proposal.read_bytes()).hexdigest(),
        newSemanticChange=False,newSoundnessCounterexampleFound=False,referenceLatestNaturalRun=11,
        checkedCases=13604,diagnosticMaxRun=33,
        nativeControl='Nine new cold controls, natural runs3..9, with no prototype adapter; typed Target continuation after NORMAL pack cut and conditional full-mark actions. Historical prefix losses remain expected-broken controls until production repair.',
        wholeAnalyzerNoFalseNegativeProof=False,wholeAnalyzerTerminationProof=False,
        productionChanged=False,selectedSemanticsChanged=False,
        scope='Neutral ordinary return cones: prefix branches, exact observations, three owners, nested strong writes, current C2/C5 and DIRECT repair. Demand from observed provisional packets prevents false harness stopping. Optimistic fresh forward sources; no full typed Target, source permission, ND, alias, static or completion scheduling model. Finite checks only; no new semantic rule.')
    experiments = {}
    expected = {'PrefixPointAudit':('AUDIT total=384','stopped=384'),
                'BranchObservationAudit':('BRANCH total=5660','unresolved=0'),
                'ThreeOwnerAudit':('THREE total=5258','unresolved=0'),
                'OverwriteObservationAudit':('OVERWRITE total=2302','unresolved=0')}
    for name, required in expected.items():
        src = pkg.parents[3]/'scripts/demand_experiments/post-direct-soundness-20261117'/(name+'.lean')
        shutil.copy2(src,out/src.name)
        checked = subprocess.run(['lean',src.name],cwd=out,env=env,text=True,capture_output=True)
        log=checked.stdout+checked.stderr
        (out/(name+'.txt')).write_text(log)
        assert checked.returncode==0 and 'warning:' not in log,log
        assert 'EARLY' not in log and 'failed=0' in log and 'nonFixed=0' in log,log
        assert all(part in log for part in required),log
        experiments[name]=dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),status='PASS',summary=log.strip())
        print('PASS',name,log.strip(),flush=True)
    receipt['experiments']=experiments
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=total_new,
        auditedDeclarations=receipt['auditedDeclarations'], modules=len(receipt['models']),
        receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
