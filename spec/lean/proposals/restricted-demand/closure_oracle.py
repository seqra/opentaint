"""Finite design oracle only. No analyzer classes or project runs."""
from collections import defaultdict, deque
import random, json, sys
from pathlib import Path

FLOW=("flow",)
def MAP(a,b): return ("map",a,b)
def static(v): return v[0] in ("s","class")
def join(a,b):
    if a==FLOW: return b
    if b==FLOW: return a
    return MAP(a[1],b[2]) if a[2]==b[1] else None

def eager(seeds,calls):
    rows=set(); todo=deque(); outgoing=defaultdict(set); incoming=defaultdict(set); parents=defaultdict(set)
    for p,c in calls: parents[c].add(p)
    def add(e):
        if e in rows:return
        rows.add(e);todo.append(e);m,a,b,label=e
        outgoing[m,a].add(e);incoming[m,b].add(e)
    for e in seeds:add(e)
    while todo:
        m,a,b,label=todo.popleft()
        if static(a) and static(b):
            for p in parents[m]:add((p,a,b,label))
        if static(b):
            for _,_,end,right in list(outgoing[m,b]):
                result=join(label,right)
                if result is not None:add((m,a,end,result))
        if static(a):
            for _,start,_,left in list(incoming[m,a]):
                result=join(left,label)
                if result is not None:add((m,start,b,result))
    return rows

def reachable(m,calls):
    children=defaultdict(list)
    for p,c in calls:children[p].append(c)
    seen={m};q=[m]
    while q:
        for c in children[q.pop()]:
            if c not in seen:seen.add(c);q.append(c)
    return seen

def factored(seeds,calls,methods):
    result=set()
    for m in methods:
        descendants=reachable(m,calls)
        visible=[e for e in seeds if e[0]==m or (e[0] in descendants and static(e[1]) and static(e[2]))]
        outgoing=defaultdict(list)
        for _,a,b,label in visible:outgoing[a].append((b,label))
        for start in list(outgoing):
            seen=set();q=deque(outgoing[start])
            while q:
                end,label=q.popleft()
                if (end,label) in seen:continue
                seen.add((end,label));result.add((m,start,end,label))
                if static(end):
                    for target,right in outgoing.get(end,()):
                        combined=join(label,right)
                        if combined is not None:q.append((target,combined))
    return result

def check(name,seeds,calls,methods,expected=(),absent=()):
    a=eager(set(seeds),set(calls));b=factored(set(seeds),set(calls),methods)
    assert a==b,(name,len(a),len(b),list(a-b)[:3],list(b-a)[:3])
    for e in expected:assert e in a,(name,"missing",e)
    for e in absent:assert e not in a,(name,"unexpected",e)
    return {"case":name,"seed_rows":len(set(seeds)),"completed_rows":len(a),"eager_equals_factored":True}

c1=("s",1);c2=("s",2);c3=("s",3);x=("n",1);y=("n",2);zero=("zero",0)
rows=[]
rows.append(check("siblings+transitive-caller+writer-reader",[(1,c1,c2,FLOW),(2,c2,c3,FLOW),(0,x,c1,FLOW),(0,c3,y,FLOW)],[(0,1),(0,2),(9,0)],[0,1,2,9],[(9,c1,c3,FLOW),(0,x,y,FLOW)]))
rows.append(check("setter-wrapper",[(0,x,c1,FLOW),(0,c1,y,FLOW)],[],[0],[(0,x,y,FLOW)]))
rows.append(check("marked-cleaner-through-FLOW-reader",[(1,c1,c2,MAP(7,7)),(0,c2,y,FLOW)],[(0,1)],[0,1],[(0,c1,y,MAP(7,7))]))
rows.append(check("incompatible-marks",[(0,x,c1,MAP(1,2)),(0,c1,y,MAP(3,4))],[],[0],absent=[(0,x,y,MAP(1,4))]))
rows.append(check("marked-round-trip-stays-colored",[(0,c1,c2,MAP(1,2)),(0,c2,c3,MAP(2,1)),(0,c1,c3,FLOW)],[],[0],[(0,c1,c3,MAP(1,1)),(0,c1,c3,FLOW)]))
rows.append(check("recursive-call-graph-and-static-cycle",[(1,c1,c2,FLOW),(2,c2,c1,FLOW),(0,x,c1,FLOW),(0,c2,y,FLOW)],[(0,1),(1,2),(2,1)],[0,1,2],[(0,x,y,FLOW)]))
rows.append(check("ordinary-middles-do-not-compose",[(0,c1,x,FLOW),(0,x,c2,FLOW)],[],[0],absent=[(0,c1,c2,FLOW)]))
rows.append(check("callee-ordinary-facts-not-imported",[(1,x,c1,FLOW),(1,c1,y,FLOW)],[(0,1)],[0,1],absent=[(0,x,y,FLOW),(0,x,c1,FLOW)]))
rows.append(check("unrelated-method-effects-not-imported",[(2,c1,c2,FLOW),(0,x,c1,FLOW),(0,c2,y,FLOW)],[(0,1)],[0,1,2],absent=[(0,x,y,FLOW)]))
rows.append(check("zero-only-from-a-real-zero-origin",[(0,zero,c1,MAP(0,7)),(0,c1,y,FLOW),(0,x,c2,FLOW)],[],[0],[(0,zero,y,MAP(0,7))],[(0,x,y,MAP(0,7))]))
rows.append(check("exact-class-marker-is-not-a-field",[(0,x,("class",1),MAP(7,7)),(0,c1,y,MAP(7,7))],[],[0],absent=[(0,x,y,MAP(7,7))]))
rng=random.Random(20261027);methods=list(range(4));vertices=[c1,c2,c3,x,y];labels=[FLOW,MAP(1,1),MAP(1,2),MAP(2,1),MAP(2,2)]
for i in range(80):
    seeds={(rng.choice(methods),rng.choice(vertices),rng.choice(vertices),rng.choice(labels))for _ in range(12)}
    calls={(rng.choice(methods),rng.choice(methods))for _ in range(5)}
    rows.append(check("random-%02d"%i,seeds,calls,methods))
# Generic exit pipeline controls. These test the design handler, not an IR adapter.
def route(normal,fact,handler):return [out for e in normal for out in handler(e,fact)]
assert route([10],("C.f",7),lambda e,f:[])==[]
assert route([], ("C.f",7),lambda e,f:[f])==[]
assert route([10,20],("C.f",7),lambda e,f:[(e,f)])==[(10,("C.f",7)),(20,("C.f",7))]
report={"state":"PASS_FINITE_DESIGN_ORACLES","seed":20261027,"graph_cases":len(rows),"random_cases":80,"exit_pipeline_controls":3,"rows":rows,"scope":"Concept/factored closure and generic exit-handler controls. No Kotlin core, JVM frontend, method actor, project or benchmark is executed."}
if len(sys.argv) > 1:
    Path(sys.argv[1]).write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({k:v for k,v in report.items()if k!="rows"},indent=2))
