#!/usr/bin/env python3
"""Audit the selected finite matching-policy model, not Kotlin implementation."""
import datetime,hashlib,importlib.util,json,os,pathlib,re,shutil,subprocess
HERE=pathlib.Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'spec/lean/lean-toolchain').is_file())
TOOLCHAIN='leanprover/lean4:v4.33.1'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 scanner_path=ROOT/'spec/lean/proposals/call-stage-result-merging-analysis-20261101/check.py'
 spec=importlib.util.spec_from_file_location('matching_scanner',scanner_path)
 scanner=importlib.util.module_from_spec(spec);spec.loader.exec_module(scanner)
 source=HERE/'Matching.lean';clean=scanner.uncomment(source.read_text())
 assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b',clean)
 assert re.findall(r'^import\s+(\S+)',clean,re.M)==['Std']
 declarations,count=scanner.declarations(source.read_text())
 pins=json.loads((HERE/'matching-reference-source-pins.json').read_text())
 for name,expected in pins['sources'].items():
  data=subprocess.check_output(['git','show',pins['baselineRevision']+':'+name],cwd=ROOT)
  assert hashlib.sha256(data).hexdigest()==expected,name
 inputs=[source,HERE/'MATCHING-README.md',HERE/'matching-check.py',HERE/'matching-reference-source-pins.json',ROOT/'spec/proof-guide.md',ROOT/'spec/impl-proposal-guide.md',ROOT/'spec/lean/lean-toolchain',scanner_path]
 before={str(p.relative_to(ROOT)):digest(p) for p in inputs}
 assert (ROOT/'spec/lean/lean-toolchain').read_text().strip()==TOOLCHAIN
 env=dict(os.environ,ELAN_TOOLCHAIN=TOOLCHAIN)
 lean=shutil.which('lean');assert lean
 version=subprocess.check_output([lean,'--version'],env=env,text=True).strip();assert 'version 4.33.1' in version
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
 work=ROOT/'spec/lean/.lake/verification/flow-antichains-directional-matching-20261105'/('matching-'+stamp)
 work.mkdir(parents=True);env['LEAN_PATH']=str(work)
 def limits():
  if hasattr(os,'sched_getaffinity'):os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
 def run(command,name,cwd):
  r=subprocess.run(command,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120,preexec_fn=limits)
  (work/name).write_text(r.stdout)
  assert r.returncode==0 and not re.search(r'\b(?:warning|error):',r.stdout),r.stdout
  return r.stdout
 run([lean,'-j','1','-M','768','-o',str(work/'Matching.olean'),str(source)],'Matching.log',HERE)
 audit=work/'Audit.lean';audit.write_text('import Matching\n'+''.join('#print axioms '+n+'\n' for n in declarations))
 out=run([lean,'-j','1','-M','768',str(audit)],'Audit.log',work)
 audited=set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",out));assert audited==set(declarations)
 axioms=set()
 for group in re.findall(r'depends on axioms: \[([^\]]*)\]',out):axioms.update(x.strip() for x in group.split(',') if x.strip())
 assert axioms<={'propext','Quot.sound'},axioms
 (HERE/'matching-audit.txt').write_text(out)
 assert before=={str(p.relative_to(ROOT)):digest(p) for p in inputs}
 receipt={'status':'SELECTED_FINITE_MODEL_PASS','selection':'ALL_STAR_STRICT_ANCESTOR_OPPOSITE_ONLY','module':'Matching.lean','theoremCount':count,'auditedPublicDeclarationCount':len(declarations),'declarations':declarations,'axioms':sorted(axioms),'noChoiceOrUnprovedAxioms':True,'executableFiniteModel':True,'inputHashes':before,'inputsStable':True,'toolchain':TOOLCHAIN,'leanVersion':version,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'productionVerifiedByKernel':False,'fullNativeAPAdapterVerified':False,'wholeEngineSafetyProved':False,'wholeDriverConvergenceProved':False,'projectPerformanceMeasured':False,'referenceBaselineRevision':pins['baselineRevision'],'audit':{'path':str((HERE/'matching-audit.txt').relative_to(ROOT)),'sha256':digest(HERE/'matching-audit.txt')},'logs':{str((work/n).relative_to(ROOT)):digest(work/n) for n in ['Matching.log','Audit.lean','Audit.log']},'limits':['Native FULL marks, E/mx, tails, domain and protection eligibility are supplied immutable finite-envelope checks, not proved native AP code.','Matching is ordered scalar membership filtering; native packed tries and split headers need adapter tests.','Complete ND product is modeled; production actor joins, keys, callback timing and work accounting are not verified.','The selected matching change is narrowing of the old matcher, not a proof of unchanged whole-engine reports.','Run1 ordinary empty-path premise law is proved conditionally on the native grammar invariant; no complete static/JVM lowering theorem.','Sibling canonicalization and relation-basis models are separate; no combined fixed-point theorem.']}
 (HERE/'matching-checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({k:receipt[k] for k in ['status','theoremCount','auditedPublicDeclarationCount','axioms','inputsStable']},indent=2))
if __name__=='__main__':main()
