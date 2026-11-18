#!/usr/bin/env python3
"""Rebuild selected approach, ordinary-write witness and uncapped recurrence."""
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess
from pathlib import Path

def main():
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
 package=Path(__file__).resolve().parent;out=a.out.resolve()
 subprocess.run(['python3',str(package.parent/'prepared-child-saved-replay-20261115'/'check.py'),'--out',str(out)],check=True)
 receipt=json.loads((out/'receipt.json').read_text())
 def compile(name):
  src=package/(name+'.lean');text=src.read_text()
  assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b',text,re.M)
  claims=re.findall(r'^\s*(?:@\[simp\]\s+)?theorem\s+(\w+)',text,re.M)
  prints=re.findall(r'^#print axioms ([\w.]+)',text,re.M)
  assert len(claims)==len(prints)and all(any(q.endswith('.'+n)for q in prints)for n in claims),(name,claims,prints)
  shutil.copy2(src,out/src.name)
  r=subprocess.run(['lean','-o',name+'.olean',src.name],cwd=out,env={**os.environ,'LEAN_PATH':str(out)},capture_output=True,text=True)
  log=r.stdout+r.stderr;(out/(name+'.txt')).write_text(log)
  if r.returncode:raise RuntimeError(name+': '+log[:3500])
  assert 'warning:'not in log,log[:1500]
  audited=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",log)
  assert len(audited)==len(claims),(name,len(audited),len(claims))
  for n,axioms in audited:assert set(axioms.replace('\n','').split(', '))-{''}<={'propext','Quot.sound'},(n,axioms)
  return name,dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),auditedDeclarations=len(audited))
 results=[compile('OverwriteReplay'),compile('OverwriteWitnesses'),compile('OverwriteConcrete')]
 with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:results+=list(pool.map(compile,[f'OverwriteCold{i}'for i in range(1,14)]))
 results+=[compile('OverwriteStable'),compile('OverwriteControl')]
 for name,result in results:receipt['models'][name]=result;receipt['auditedDeclarations']+=result['auditedDeclarations']
 added=sum(r['auditedDeclarations']for _,r in results)
 receipt['scope']='Selected prepared-child replay plus native-audited ordinary pre/post overwrites; complete cold runs1-13, E-aware NORMAL precoverage, stable C2/C5 packet for every later field limit, concrete caller closure and fresh ZERO/Target recurrence without an iteration cap. Scoped return-cone reference, not whole-core simulation.'
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',newDeclarations=added,modules=len(receipt['models']),auditedDeclarations=receipt['auditedDeclarations'],receipt=str(out/'receipt.json')),indent=2))
if __name__=='__main__':main()
