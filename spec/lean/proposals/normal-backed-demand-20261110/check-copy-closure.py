from pathlib import Path
import json,collections,gzip,hashlib
import argparse
ROOT=next(d for d in Path(__file__).resolve().parents if(d/'spec/lean/lean-toolchain').is_file())
parser=argparse.ArgumentParser()
parser.add_argument('--output-directory',type=Path,required=True)
args=parser.parse_args();p=args.output_directory;p.mkdir(parents=True,exist_ok=True)
sourceBytes=gzip.open(ROOT/'docs/reports/data/bidirectional-owasp-copy-forms-20261110.jsonl.gz','rb').read()
rows=[json.loads(l)for l in sourceBytes.splitlines()]
F={q['id']:q['name']for d in rows for q in d.get('fields',[])}
def pat(q):return(q['base'],tuple(F[i]for i in q['path']))
def parsebase(s):return set(x.strip()for x in s[1:-1].split(',')) if s!='[]'else set()
# One forward form snapshot per instruction, repeated cache rebuilds checked separately.
H={};E=collections.defaultdict(list);P={};ST=collections.defaultdict(list)
for d in rows:
 i=d.get('instruction');ev=d['event']
 if ev=='PLAN_HEADER':P.setdefault(i,d)
 if ev=='PLAN_STAGE':
  if not any(s['stage']==d['stage']for s in ST[i]):ST[i].append(d)
 if ev=='FORM_HEADER':
  key=(i,d['stage'])
  if key in H: assert all(H[key][z]==d[z]for z in['sources','conjunctions','staticOperations','touchedValues']), 'Changed form structure'
  H.setdefault(key,d)
 if ev=='FORM_EDGE':
  if d['from']['mark']['kind']=='FLOW':
   assert d['to']['mark']['kind']=='FLOW'and d['from']['tail']==d['to']['tail']=='STAR'and not d['may']and not d['conjunctive']and d['sharedExclusion']=='Empty'
   assert not d['from']['E'] and not d['to']['E'] and not d['from']['mark']['mx'] and not d['to']['mark']['mx']
   r=pat(d['from'])+pat(d['to']);
   if r not in E[i,d['stage']]:E[i,d['stage']].append(r)
  else:assert d['from']['base']=='<zero>'and d['to']['base']=='<zero>'
for h in H.values():assert all(h[k]==0for k in['sources','conjunctions','staticOperations'])
for st in [s for ss in ST.values()for s in ss]:assert st['stage'].split(':')[1]in['Edges','Actions']and st.get('steps','[]')=='[]'
# r=(inputBase,inputPrefix,outputBase,outputPrefix), every suffix is correlated.
def compose(a,c):
 if a[2]!=c[0]:return None
 q,u=a[3],c[1]
 if q[:len(u)]==u:return(a[0],a[1],c[2],c[3]+q[len(u):])
 if u[:len(q)]==q:return(a[0],a[1]+u[len(q):],c[2],c[3])
 return None
def step(i,stage,rs):
 touched=parsebase(H[i,stage]['touchedValues']);out=set()
 for r in rs:
  if r[2]not in touched:out.add(r)
  else:
   for e in E[i,stage]:
    v=compose(r,e)
    if v:out.add(v)
 return out
def call(i,rs):
 plan=P[i];at=collections.defaultdict(set);at[plan['entry']].update(rs)
 # finite DAG of six CallPoint values; each edge increases enum order in forward forms.
 for pt in['BEFORE','BOUND','ADDED','RETURNED','REWRITTEN','AFTER']:
  for st in ST[i]:
   if st['from']!=pt:continue
   out=step(i,st['stage'],at[pt])if st['stage'].split(':')[1]=='Edges'else at[pt]
   at[st['to']].update(out)
 return at[plan['exit']]
rs={('arg(1)',(),'arg(1)',())};sizes=[]
for i in range(10):
 rs=call(i,rs)if i in P else step(i,'STATEMENT',rs)
 sizes.append((i,len(rs)))
ret=sorted(r for r in rs if r[2]=='ret')
print('sizes',sizes,'return rows',len(ret))
# Source of the normal basis is the previously captured accepted runtime; resolve accessors by labels.
x=json.load(open(ROOT/'docs/reports/data/bidirectional-owasp-helper-cycle-20261110.json'))
Fs=x['analysis']['fields'];runs=x['analysis']['runs']
def nr(r):
 a=r['premise'];c=r['conclusion']
 if len(a)!=1 or a[0]['mark']['kind']!='FLOW'or a[0]['tail']!='STAR'or c['tail']!='STAR'or c['layer']!='NORMAL':return None
 return(a[0]['base'],tuple(Fs[str(i)]for i in a[0]['path']),c['base'],tuple(Fs[str(i)]for i in c['path']))
def rev(r):return(r[2],r[3],r[0],r[1])
def covers(s,r):
 if s[0]!=r[0]or s[2]!=r[2]or r[1][:len(s[1])]!=s[1]:return False
 return r[3]==s[3]+r[1][len(s[1]):]
checks=[]
for run in range(7,12):
 # Current plus saved before: this equals the family retained after the completed barrier for this scope.
 rr=runs[str(run)];basis=[]
 for r in rr['persistedBefore']:
  v=nr(r)
  if v:basis.append((r['nativeDirection'],v))
 for r in rr['summaries']:
  v=nr(r)
  if v:basis.append(('FORWARD'if run%2 else'BACKWARD',v))
 missingF=[r for r in ret if not any(covers(s if d=='FORWARD'else rev(s),r)for d,s in basis)]
 missingB=[r for r in ret if not any(covers(s if d=='BACKWARD'else rev(s),rev(r))for d,s in basis)]
 c={'run':run,'returnRows':len(ret),'missingForward':missingF,'missingBackward':missingB};checks.append(c)
 print(run,'missing',len(missingF),len(missingB))
 for r in missingF[:4]:print(' missing F',r)
 for r in missingB[:4]:print(' missing B',r)
result={'schema':'normal-backed-copy-closure-v1','formEnd':rows[-1],'formSourceSha256':hashlib.sha256(sourceBytes).hexdigest(),'scope':'Non-null arm of the selected helper, all positive-copy DATA paths; guards/filters ignored for a conservative over-approximation. The null arm returns a constant and has no parameter-to-return flow. Does not model concrete rule observations, ZERO, Target or source permission scheduling.','stageSizes':sizes,'returnRows':ret,'checks':checks,'normalBasisOrigin':'bidirectional-owasp-helper-cycle-20261110.json'}
(p/'copy-closure.json').write_text(json.dumps(result,indent=2)+'\n')

# Use the actual retained NORMAL native records after each barrier, not a union
# that could contain already-compacted old rows.
raw_native=repo_native=ROOT/'docs/reports/data/bidirectional-owasp-helper-cycle-20261110.jsonl.gz'
after_basis=collections.defaultdict(list)
for line in gzip.open(raw_native,'rt'):
 d=json.loads(line)
 if d.get('event')!='PERSISTED_AFTER':continue
 aa=d['premise']['members'];c=d['facts']
 if len(aa)!=1 or aa[0]['mark']['kind']!='FLOW'or aa[0]['tail']!='STAR'or c['kind']!='FLOW'or c['tail']!='STAR':continue
 assert c['layer']=='NORMAL'
 assert not aa[0]['E']and not aa[0]['mark']['mx']and not c['E']and not c['mx']
 ff={r['id']:r['name']for r in d['fields']};nodes={r['id']:r for r in d['nodes']}
 def walk(n,path):
  v=nodes[n];out=[path]if v['flowLeaf']else[]
  for z in v['children']:out+=walk(z['node'],path+(ff[z['field']],))
  return out
 for path0 in walk(c['root'],()):
  after_basis[d['run']].append((d['nativeDirection'],(aa[0]['base'],tuple(ff[i]for i in aa[0]['path']),c['base'],path0)))

# P(X): complete clipped copy relation, with retained replay and universal STAR-match coverage.
per_edge=[]
for run in range(7,12):
 rr=runs[str(run)];direction='FORWARD'if run%2 else'BACKWARD';base=after_basis[run]
 matrix=ret if run%2 else[rev(r)for r in ret]
 for d in [s for s in rr['summaries']if s['conclusion']['layer']=='DEMAND']:
  a=d['premise'][0];c=d['conclusion'];assert a['tail']=='STAR'and c['tail']=='ANY'and a['mark']['kind']==c['mark']['kind']=='FLOW'
  ip=tuple(Fs[str(i)]for i in a['path']);op=tuple(Fs[str(i)]for i in c['path'])
  before=(a['base'],ip,a['base'],ip);after=(c['base'],op,c['base'],op)
  origins=set()
  for r in matrix:
   k=compose(before,r)
   k=compose(k,after)if k else None
   if k:origins.add(k)
  proof=[];missing=[]
  for r in sorted(origins):
   ws=[]
   for nd,n in base:
    view=n if nd==direction else rev(n)
    star_ok=nd!=direction or ip[:len(view[1])]==view[1]
    if star_ok and covers(view,r):ws.append({'nativeDirection':nd,'native':n,'view':view,'role':'SAVED_DIRECT'if nd==direction else'SAVED_OPPOSITE','shift':r[1][len(view[1]):]})
   if ws:
    proof.append({'origin':r,'witness':min(ws,key=lambda w:(w['role']!='SAVED_DIRECT',len(w['view'][1])))})
   else:missing.append(r)
  q={'run':run,'demand':d,'originCount':len(origins),'complete':True,'missing':missing,'P':bool(origins)and not missing,'certificates':proof};per_edge.append(q)
  print('P',run,a['path'],c['path'],len(origins),not missing,'missing',missing[:1])
result['perEdge']=per_edge
(p/'copy-closure.json').write_text(json.dumps(result,indent=2)+'\n')
