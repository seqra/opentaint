#!/usr/bin/env python3
"""Check constructive prefix cover, progress and complete cold AP traces."""
import argparse,hashlib,json,os,re,shutil,subprocess,concurrent.futures
from pathlib import Path

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True);args=parser.parse_args()
 package=Path(__file__).resolve().parent;out=args.out.resolve()
 subprocess.run(['python3',str(package.parent/'nested-saved-replay-cycle-20261114'/'check.py'),'--out',str(out)],check=True)
 receipt=json.loads((out/'receipt.json').read_text())
 def compile(name):
  src=package/(name+'.lean');contents=src.read_text()
  assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b',contents,re.M)
  claims=re.findall(r'^\s*(?:@\[simp\]\s+)?theorem\s+(\w+)',contents,re.M);printed=re.findall(r'^#print axioms ([\w.]+)',contents,re.M)
  assert len(claims)==len(printed)and all(any(n.endswith('.'+c)for n in printed)for c in claims)
  shutil.copy2(src,out/src.name)
  r=subprocess.run(['lean','-o',name+'.olean',src.name],cwd=out,env={**os.environ,'LEAN_PATH':str(out)},capture_output=True,text=True)
  log=r.stdout+r.stderr;(out/(name+'.txt')).write_text(log)
  if r.returncode:raise RuntimeError(f'{name}: {log[:4000]}')
  assert 'warning:'not in log,log[:2000]
  audited=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",log)
  assert len(audited)==len(claims),(name,len(audited),len(claims))
  for n,axioms in audited:assert set(axioms.replace('\n','').split(', '))-{''}<={'propext','Quot.sound'},(n,axioms)
  return name,dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),auditedDeclarations=len(audited))
 results=[compile('PartitionCover'),compile('PartitionMachine'),compile('Compatibility')]
 modules=sorted(p.stem for p in package.glob('Certificate*.lean'))
 with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:results+=list(pool.map(compile,modules))
 for name,model in results:receipt['models'][name]=model;receipt['auditedDeclarations']+=model['auditedDeclarations']
 added=sum(x['auditedDeclarations']for _,x in results)
 receipt['scope']='Persistent input partition cover and bounded progress; separate owners retained; complete cold prefix/postfix/double-call and old positive references; actual-original replay, backward producer permission and DATA/Target frontier checked. No universal native termination claim.'
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',newDeclarations=added,modules=len(receipt['models']),auditedDeclarations=receipt['auditedDeclarations'],receipt=str(out/'receipt.json')),indent=2))
if __name__=='__main__':main()
