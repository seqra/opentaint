#!/usr/bin/env python3
"""Constructive certificate check for the complete old/new acceptance set."""
import argparse,hashlib,json,os,re,shutil,subprocess
from pathlib import Path

def main():
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args();package=Path(__file__).resolve().parent;out=a.out.resolve()
 subprocess.run(['python3',str(package.parent/'nested-saved-replay-cycle-20261114'/'check.py'),'--out',str(out)],check=True)
 receipt=json.loads((out/'receipt.json').read_text());added=0
 for name in ['OwnerProjection','DirectMachine','ProxyCertificates','ProxyAcceptance']:
  src=package/(name+'.lean');contents=src.read_text()
  assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b',contents,re.M)
  claims=re.findall(r'^\s*(?:@\[simp\]\s+)?theorem\s+(\w+)',contents,re.M);printed=re.findall(r'^#print axioms ([\w.]+)',contents,re.M)
  assert len(claims)==len(printed) and all(any(n.endswith('.'+c)for n in printed)for c in claims)
  shutil.copy2(src,out/src.name)
  r=subprocess.run(['lean','-o',name+'.olean',src.name],cwd=out,env={**os.environ,'LEAN_PATH':str(out)},capture_output=True,text=True);log=r.stdout+r.stderr;(out/(name+'.txt')).write_text(log)
  if r.returncode:print(log);raise SystemExit(r.returncode)
  assert 'warning:'not in log,log
  audited=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",log)
  assert len(audited)==len(claims)
  for n,axioms in audited:assert set(axioms.replace('\n','').split(', '))-{''}<={'propext','Quot.sound'},(n,axioms)
  receipt['models'][name]=dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),auditedDeclarations=len(audited));receipt['auditedDeclarations']+=len(audited);added+=len(audited)
 receipt['scope']='Transparent forwarder semantic equivalence, guarded fallback for all old examples, complete new cold trace and natural run-9 stop with normal observation; original counter and earlier approach proofs rechecked'
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',newDeclarations=added,modules=len(receipt['models']),auditedDeclarations=receipt['auditedDeclarations'],receipt=str(out/'receipt.json')),indent=2))
if __name__=='__main__':main()
