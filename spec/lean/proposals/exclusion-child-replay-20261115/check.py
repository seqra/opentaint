#!/usr/bin/env python3
"""Constructive exclusion cover, fixed-plan cost, all cold acceptance traces."""
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess
from pathlib import Path

def main():
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
 package=Path(__file__).resolve().parent;out=a.out.resolve()
 subprocess.run(['python3',str(package.parent/'overwrite-saved-replay-cycle-20261115'/'check.py'),'--out',str(out)],check=True)
 receipt=json.loads((out/'receipt.json').read_text())
 def compile(name):
  src=package/(name+'.lean');contents=src.read_text()
  assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b',contents,re.M)
  claims=re.findall(r'^\s*(?:@\[simp\]\s+)?theorem\s+(\w+)',contents,re.M);prints=re.findall(r'^#print axioms ([\w.]+)',contents,re.M)
  assert len(claims)==len(prints)and all(any(n.endswith('.'+c)for n in prints)for c in claims)
  shutil.copy2(src,out/src.name)
  r=subprocess.run(['lean','-o',name+'.olean',src.name],cwd=out,env={**os.environ,'LEAN_PATH':str(out)},capture_output=True,text=True)
  log=r.stdout+r.stderr;(out/(name+'.txt')).write_text(log)
  if r.returncode:raise RuntimeError(name+': '+log[:4500])
  assert 'warning:'not in log,log[:2000]
  audited=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",log)
  assert len(audited)==len(claims),(name,len(audited),len(claims))
  for n,axioms in audited:assert set(axioms.replace('\n','').split(', '))-{''}<={'propext','Quot.sound'},(n,axioms)
  return name,dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),auditedDeclarations=len(audited))
 results=[compile('ExclusionRoutedCalls'),compile('ExclusionCover'),compile('ExclusionCompatibility')]
 with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:
  results+=list(pool.map(compile,sorted(p.stem for p in package.glob('ExclusionCertificate*.lean'))))
 for name,item in results:receipt['models'][name]=item;receipt['auditedDeclarations']+=item['auditedDeclarations']
 added=sum(v['auditedDeclarations']for _,v in results)
 receipt['scope']='Existing prepared child cover with native operand/record field exclusions; arbitrary concrete E-aware reader cover, qualified output service, fixed-plan no-extra-work, fallback laws, complete cold old/new references, natural ZERO/Target stop, exact growth-control equality. Not universal native termination or whole-run cardinality.'
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',newDeclarations=added,auditedDeclarations=receipt['auditedDeclarations'],modules=len(receipt['models']),receipt=str(out/'receipt.json')),indent=2))
if __name__=='__main__':main()
