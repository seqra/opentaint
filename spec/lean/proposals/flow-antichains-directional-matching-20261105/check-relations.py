#!/usr/bin/env python3
"""Check only Relations.lean; no Kotlin/native adapter proof is implied."""
import datetime,hashlib,importlib.util,json,os,re,shutil,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if(p/'spec/lean/lean-toolchain').is_file())
TOOLCHAIN='leanprover/lean4:v4.33.1'
BASELINE='52f32dd437d438aec4a700a02c18d94c31d58093'
COMMON='core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/'
REFERENCES=[COMMON+p for p in ['store/RunSummaries.kt','store/FlowBackedSummaries.kt','store/RecordStore.kt',
    'store/PathTrie.kt','ap/Reference.kt','ap/Groups.kt','ap/Summary.kt','ap/ApOps.kt',
    'engine/PublicationIndex.kt','engine/BlockSummaryLinks.kt','engine/MethodBlockRuntime.kt',
    'engine/LocalRelationApplication.kt','engine/LoopOutputRestriction.kt']]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    scanpath=ROOT/'spec/lean/proposals/call-stage-result-merging-analysis-20261101/check.py'
    spec=importlib.util.spec_from_file_location('relation_scanner',scanpath);scanner=importlib.util.module_from_spec(spec);spec.loader.exec_module(scanner)
    source=HERE/'Relations.lean';clean=scanner.uncomment(source.read_text())
    assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b',clean)
    assert re.findall(r'^import\s+(\S+)',clean,re.M)==['Std']
    declarations,theorems=scanner.declarations(source.read_text())
    for name,fields in [('Row',['interface','inputBase','outputBase','inputPrefix','outputPrefix']),
        ('Pair',['interface','inputBase','outputBase','mark','inputPath','outputPath']),
        ('Factors',['inputCore','outputCore','residual'])]:
        declarations+=['FlowAntichains.Relations.'+name,'FlowAntichains.Relations.'+name+'.mk']
        declarations+=['FlowAntichains.Relations.'+name+'.'+field for field in fields]
    declarations+=['FlowAntichains.Relations.instDecidableEqRow','FlowAntichains.Relations.instDecidableEqFactors']
    pins={}
    for relative in REFERENCES:
        data=subprocess.check_output(['git','show',BASELINE+':'+relative],cwd=ROOT)
        expected=hashlib.sha256(data).hexdigest();assert sha(ROOT/relative)==expected; pins[relative]=expected
    inputs=[source,HERE/'check-relations.py',scanpath]+[ROOT/p for p in REFERENCES]
    before={str(p.relative_to(ROOT)):sha(p)for p in inputs}
    lean=shutil.which('lean');assert lean
    env=dict(os.environ,ELAN_TOOLCHAIN=TOOLCHAIN);version=subprocess.check_output([lean,'--version'],env=env,text=True).strip()
    assert re.search(r'version 4\.33\.1\b',version)
    work=HERE/'.verification-relations'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ');work.mkdir(parents=True)
    env['LEAN_PATH']=str(work)
    def cpu():
        if hasattr(os,'sched_getaffinity'):os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
    def run(args,name,cwd):
        result=subprocess.run(args,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120,preexec_fn=cpu)
        (work/name).write_text(result.stdout);assert result.returncode==0 and not re.search(r'\b(?:warning|error):',result.stdout),result.stdout
        return result.stdout
    run([lean,'-j','1','-M','768','-o',str(work/'Relations.olean'),str(source)],'compile.log',HERE)
    audit=work/'AuditRelations.lean';audit.write_text('import Relations\n'+''.join('#print axioms '+name+'\n'for name in declarations))
    output=run([lean,'-j','1','-M','768',str(audit)],'audit.log',work)
    audited=set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",output));assert audited==set(declarations)
    axioms=set()
    for group in re.findall(r'depends on axioms: \[([^\]]*)\]',output):axioms.update(a.strip()for a in group.split(',')if a.strip())
    assert axioms<={'propext','Quot.sound'},axioms
    (HERE/'relations-audit.txt').write_text(output)
    assert before=={str(p.relative_to(ROOT)):sha(p)for p in inputs}
    receipt={'status':'NORMAL_RELATION_ANTICHAIN_MODEL_PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'module':'Relations','namespace':'FlowAntichains.Relations','toolchain':TOOLCHAIN,'leanVersion':version,
        'theoremCount':theorems,'auditedDeclarationCount':len(declarations),'declarations':declarations,'axioms':sorted(axioms),
        'activeCPUs':1,'memoryLimitMiB':768,'allExplicitPublicDeclarationsAudited':True,'inputsStable':True,
        'baselineRevision':BASELINE,'referenceSourceHashes':pins,'inputHashes':before,
        'nativeAPAdapterProved':False,'efficientNativeTrieAdapterProved':False,'driverOrCallbackEquivalenceProved':False,
        'runtimeModified':False,'newNativeJvmOrAnalyzerRun':False,
        'proved':['Concrete aligned STAR inclusion and forward/reverse growth invariance',
            'Executable common-suffix factoring reconstructs actual endpoint paths',
            'Family-key equality plus residual-prefix membership is equivalent to exact aligned cover',
            'Executable prefix-list candidate query is complete and sound for that cover',
            'Online canonicalizer keeps a pairwise antichain, never invents rows, and preserves the full concrete relation',
            'Shared below-prefix payload transformations preserve ordered application results'],
        'limits':['Header/interface is an opaque exact key; native E-empty/mx/owner/port eligibility is an adapter obligation.',
            'Prefix-list reference proves trie query semantics, not native child-map complexity or packed DAG mutation.',
            'Payload bridge requires native below-prefix transfer correspondence; ancestor/inside, callbacks, C2 and observer quotient are separate modules/adapter obligations.',
            'Already-delivered valid subset effects are not retracted; no raw-refinement history or weak-row synthesis is modeled.'],
        'portableAuditSha256':sha(HERE/'relations-audit.txt'),
        'logs':{str(p.relative_to(ROOT)):sha(p)for p in [work/'compile.log',work/'AuditRelations.lean',work/'audit.log']}}
    (HERE/'relations-checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({key:receipt[key]for key in ['status','theoremCount','auditedDeclarationCount','axioms','inputsStable']},indent=2))
if __name__=='__main__':main()
