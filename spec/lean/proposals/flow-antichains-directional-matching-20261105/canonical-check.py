#!/usr/bin/env python3
"""Audit the selected finite canonical-region model, not Kotlin implementation."""
import datetime,hashlib,importlib.util,json,os,pathlib,re,shutil,subprocess
HERE=pathlib.Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'spec/lean/lean-toolchain').is_file())
TOOLCHAIN='leanprover/lean4:v4.33.1'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 scanner_path=ROOT/'spec/lean/proposals/call-stage-result-merging-analysis-20261101/check.py'
 spec=importlib.util.spec_from_file_location('canonical_scanner',scanner_path)
 scanner=importlib.util.module_from_spec(spec);spec.loader.exec_module(scanner)
 source=HERE/'Canonical.lean';clean=scanner.uncomment(source.read_text())
 assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b',clean)
 assert re.findall(r'^import\s+(\S+)',clean,re.M)==['Std']
 declarations,count=scanner.declarations(source.read_text())
 pins=json.loads((HERE/'canonical-reference-source-pins.json').read_text())
 for name,expected in pins['sources'].items():
  data=subprocess.check_output(['git','show',pins['baselineRevision']+':'+name],cwd=ROOT)
  assert hashlib.sha256(data).hexdigest()==expected,name
 inputs=[source,HERE/'canonical-check.py',HERE/'canonical-reference-source-pins.json',ROOT/'spec/proof-guide.md',ROOT/'spec/impl-proposal-guide.md',ROOT/'spec/lean/lean-toolchain',scanner_path]
 before={str(p.relative_to(ROOT)):digest(p) for p in inputs}
 assert (ROOT/'spec/lean/lean-toolchain').read_text().strip()==TOOLCHAIN
 env=dict(os.environ,ELAN_TOOLCHAIN=TOOLCHAIN)
 lean=shutil.which('lean');assert lean
 version=subprocess.check_output([lean,'--version'],env=env,text=True).strip();assert 'version 4.33.1' in version
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
 work=ROOT/'spec/lean/.lake/verification/flow-antichains-directional-matching-20261105'/('canonical-'+stamp)
 work.mkdir(parents=True);env['LEAN_PATH']=str(work)
 def limits():
  if hasattr(os,'sched_getaffinity'):os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
 def run(command,name,cwd):
  r=subprocess.run(command,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120,preexec_fn=limits)
  (work/name).write_text(r.stdout)
  assert r.returncode==0 and not re.search(r'\b(?:warning|error):',r.stdout),r.stdout
  return r.stdout
 run([lean,'-j','1','-M','1024','-o',str(work/'Canonical.olean'),str(source)],'Canonical.log',HERE)
 audit=work/'Audit.lean';audit.write_text('import Canonical\n'+''.join('#print axioms '+n+'\n' for n in declarations))
 out=run([lean,'-j','1','-M','1024',str(audit)],'Audit.log',work)
 audited=set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",out));assert audited==set(declarations)
 axioms=set()
 for group in re.findall(r'depends on axioms: \[([^\]]*)\]',out):axioms.update(x.strip() for x in group.split(',') if x.strip())
 assert axioms<={'propext','Quot.sound'},axioms
 (HERE/'canonical-audit.txt').write_text(out)
 assert before=={str(p.relative_to(ROOT)):digest(p) for p in inputs}
 receipt={'status':'SELECTED_FINITE_MODEL_PASS','selection':'CANONICAL_ONLY_C2_CROSS_E_MUST_REFILL_REVERSE_OVERLAP','module':'Canonical.lean','theoremCount':count,'auditedPublicDeclarationCount':len(declarations),'declarations':declarations,'axioms':sorted(axioms),'noChoiceOrUnprovedAxioms':True,'executableFiniteModel':True,'inputHashes':before,'inputsStable':True,'toolchain':TOOLCHAIN,'leanVersion':version,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'productionVerifiedByKernel':False,'fullNativeAPAdapterVerified':False,'wholeEngineSafetyProved':False,'wholeDriverConvergenceProved':False,'projectPerformanceMeasured':False,'referenceBaselineRevision':pins['baselineRevision'],'audit':{'path':str((HERE/'canonical-audit.txt').relative_to(ROOT)),'sha256':digest(HERE/'canonical-audit.txt')},'logs':{str((work/n).relative_to(ROOT)):digest(work/n) for n in ['Canonical.log','Audit.lean','Audit.log']},'limits':['The executable finite model uses exact atomized keys and rooted first-field exclusions; native Flow/Taint/DAG encoding is not kernel-verified.','The key scope is opaque exact equality. Production adapters must include full premise, ports, direction, layer, kind, base and mark/protection support.','Header-index candidate-count savings are proved; whole-trie/JVM memory, throughput and complexity are not measured or verified.','Canonical-only C2 is a selected semantic change. This model does not prove equality with historical uncanonicalized C2 outputs.','Spatial union preservation does not prove unchanged next-run refinement pairs, source/sink reports or whole-driver convergence.','Reverse overlap geometry is proved sound and complete. MUST-derived opposite provenance, mark/mx/native inverse-result and callback/layer adapters require native tests.','List-reference normal forms are idempotent; native ordered interner serialization and unique shape across arbitrary E list order are not proved.']}
 (HERE/'canonical-checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({k:receipt[k] for k in ['status','theoremCount','auditedPublicDeclarationCount','axioms','inputsStable']},indent=2))
if __name__=='__main__':main()
