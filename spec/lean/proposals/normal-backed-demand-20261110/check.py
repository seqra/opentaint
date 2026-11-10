#!/usr/bin/env python3
"""Repeat scoped design checks; no production runtime edits or project rerun."""
from pathlib import Path
import argparse,datetime,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if(p/'spec/lean/lean-toolchain').is_file())
a=argparse.ArgumentParser();a.add_argument('--output-directory',type=Path,required=True);args=a.parse_args();out=args.output_directory.resolve();out.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert (ROOT/'spec/lean/lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1'
logs=[]
for name in['NormalBackedDemand','ObservedCertificates']:
 p=HERE/(name+'.lean');source=p.read_text()
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|\bClassical\.|^\s*axiom\b',source,re.M)
 log=out/(name+'.log');cmd=['lake','env','lean',str(p)];r=subprocess.run(cmd,cwd=ROOT/'spec/lean',text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_text(r.stdout);assert r.returncode==0,r.stdout
 assert 'Classical.choice'not in r.stdout
 logs.append({'command':cmd,'exitCode':r.returncode,'log':log.name,'sha256':sha(log)})
# Audit every generic theorem, not just the main declarations printed in the model.
s=(HERE/'NormalBackedDemand.lean').read_text();names=re.findall(r'^theorem (\w+)',s,re.M);audit=out/'Audit.lean';audit.write_text(s+'\n'+'\n'.join('#print axioms NormalBackedDemand.'+n for n in names)+'\n');r=subprocess.run(['lake','env','lean',str(audit)],cwd=ROOT/'spec/lean',text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(out/'axioms.log').write_text(r.stdout);assert r.returncode==0,r.stdout
for line in r.stdout.splitlines():
 if 'depends on axioms:'in line:
  axioms=set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',line.split('depends on axioms:')[1]));assert axioms<=set(['propext','Quot.sound']),axioms
r=subprocess.run([sys.executable,str(HERE/'check-copy-closure.py'),'--output-directory',str(out)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(out/'copy-closure.log').write_text(r.stdout);assert r.returncode==0,r.stdout
x=json.loads((out/'copy-closure.json').read_text());assert len(x['returnRows'])==12 and len(x['perEdge'])==34 and all(e['P']for e in x['perEdge'])
receipt={'createdAt':datetime.datetime.now(datetime.timezone.utc).isoformat(),'runtime':'14d7b63369d94f49d4c551be8405ed7719f267cc','latestReachedRun':11,'latestCompletedRun':11,'latestAcceptedForwardRun':11,'productionChanges':False,'genericTheorems':len(names),'observedCertificates':34,'clippedOrigins':sum(e['originCount']for e in x['perEdge']),'allSelectedEdgesPass':True,'modelChecks':logs,'axiomAudit':{'log':'axioms.log','sha256':sha(out/'axioms.log'),'allowed':['propext','Quot.sound']},'sourceHashes':{p.name:sha(p)for p in HERE.iterdir()if p.is_file()and p.suffix in['.lean','.py','.kt','.gradle']},'nativeAnalyzerProved':False,'arbitraryScopeCompletenessProved':False,'retirementImplemented':False,'scope':'Constructive prefix relation/native replay certificates; source-checked finite pure-copy DATA graph of the selected OWASP helper. Concrete/Zero/Target observations and native runtime require the stated existing contracts.'}
(out/'checks.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k]for k in['genericTheorems','observedCertificates','clippedOrigins','allSelectedEdgesPass']}))
