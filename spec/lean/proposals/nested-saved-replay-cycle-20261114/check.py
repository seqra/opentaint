#!/usr/bin/env python3
"""Recheck the cold trace and uncapped nested-replay recurrence constructively."""
import argparse, hashlib, json, os, re, shutil, subprocess
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parent;out=a.out.resolve()
    previous=package.parent/'same-lane-uniform-termination-20261114'
    subprocess.run(['python3',str(previous/'check.py'),'--out',str(out)],check=True)
    receipt_path=out/'receipt.json';receipt=json.loads(receipt_path.read_text());added=0
    for name in ['TargetZeroKernel','SavedReplayCycle','StablePackets','ColdMachine','ColdCertificates','CallerClosure','TargetClosure']:
        src=(package.parent/'constant-filter-target-zero-20261031' if name=='TargetZeroKernel' else package)/(name+'.lean');contents=src.read_text()
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b',contents,re.M)
        claims=re.findall(r'^\s*(?:@\[simp\]\s+)?theorem\s+(\w+)',contents,re.M)
        printed=re.findall(r'^#print axioms ([\w.]+)',contents,re.M)
        if name != 'TargetZeroKernel': assert len(claims)==len(printed),(name,claims,printed)
        if name != 'TargetZeroKernel': assert all(any(n.endswith('.'+c)for n in printed)for c in claims)
        shutil.copy2(src,out/src.name)
        if name == 'TargetZeroKernel':
            import importlib.util
            helper_path=src.parent/'check.py'
            spec=importlib.util.spec_from_file_location('old_target_checker',helper_path)
            helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
            declared,_=helper.declarations(contents)
            qualified=[n for n in declared if n.rsplit('.',1)[-1] in claims]
            with (out/src.name).open('a') as f:
                for claim in qualified: f.write('\n#print axioms '+claim+'\n')
        r=subprocess.run(['lean']+(['-Dlinter.deprecated=false'] if name=='TargetZeroKernel' else [])+['-o',name+'.olean',src.name],cwd=out,
            env={**os.environ,'LEAN_PATH':str(out)},capture_output=True,text=True)
        log=r.stdout+r.stderr;(out/(name+'.txt')).write_text(log)
        if r.returncode:print(log);raise SystemExit(r.returncode)
        assert 'warning:'not in log,log
        audited=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",log)
        audited=list(dict(audited).items())
        if name == 'TargetZeroKernel':
            assert set(qualified) <= {n for n,_ in audited}
        else: assert len(audited)==len(claims),(name,len(audited),len(claims))
        for n,axioms in audited:
            assert set(axioms.replace('\n','').split(', '))-{''}<={'propext','Quot.sound'},(n,axioms)
        receipt['models'][name]=dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),auditedDeclarations=len(audited))
        receipt['auditedDeclarations']+=len(audited)
        if name != 'TargetZeroKernel': added+=len(audited)
    receipt['scope']='Unchanged saved replay: cold runs 1–9, complete stationary C2/C5 packets, caller closure, same-lane coverage rejection, uncapped nonempty demand recurrence'
    receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',newDeclarations=added,modules=len(receipt['models']),auditedDeclarations=receipt['auditedDeclarations'],receipt=str(receipt_path)),indent=2))
if __name__=='__main__':main()
