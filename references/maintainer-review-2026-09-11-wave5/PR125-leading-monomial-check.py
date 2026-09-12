"""Independent finite stress check of Hall's shared-variable polynomial recursion.
Pure standard library; writes only an adjacent evidence JSON. No general theorem
is inferred from these finite checks.
"""
from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path
import json

def add_term(p,m,c,ways):
 a,b=p.get(m,(0,0));p[m]=(a+c,b+ways)
def mul(p,q):
 out={}
 for m,(a,b) in p.items():
  for n,(c,d) in q.items():add_term(out,tuple(sorted(m+n)),a*c,b*d)
 return out

def analyze(n,edges,d=None,expect=True):
 W=[[i for i in range(j) if (i,j) not in edges] for j in range(n)]
 if d is None:d=len(W[-1])+1
 vars=[(j,cs) for j in range(n) for cs in combinations(range(d),len(W[j])+1)]
 ids={v:i for i,v in enumerate(vars)}
 v=[]
 for j in range(n):
  out=[{} for _ in range(d)]
  for t in range(d):
   for iset in permutations([i for i in range(d) if i!=t],len(W[j])):
    labels=iset+(t,)
    sign=(-1)**sum(labels[a]>labels[b] for a in range(len(labels)) for b in range(a+1,len(labels)))
    m=(ids[(j,tuple(sorted(labels)))],);p={m:(sign,1)}
    for w,idx in zip(W[j],iset):p=mul(p,v[w][idx])
    for m,(c,k) in p.items():add_term(out[t],m,c,k)
  v.append(out)
 checks=[]
 for i in range(n):
  for j in range(i,n):
   p={}
   for t in range(d):
    for m,(c,k) in mul(v[i][t],v[j][t]).items():add_term(p,m,c,k)
   edge=i==j or (i,j) in edges
   if not edge:assert all(c==0 for c,k in p.values())
   if edge and expect:
    def priority(m):
     c=Counter(m);return tuple(c.get(s,0) for s in range(len(vars)))
    lead=max(p,key=priority);coef,ways=p[lead]
    assert ways==1 and abs(coef)==1,(n,edges,i,j,coef,ways)
    checks.append({'pair':[i,j],'leading_coefficient':coef,'expanded_occurrences':ways})
   elif edge:checks.append({'pair':[i,j],'nonzero':any(c!=0 for c,k in p.values())})
 return checks

def greedy(n,E):
 for i in range(n):
  a=sum((h,i) in E for h in range(i))
  if any(sum((h,j) in E for h in range(i))>a for j in range(i,n)):return False
 return True

counts={'greedy_ordered_graphs':0,'unique_leading_checks':0};cases=[]
for n in range(1,5):
 pairs=list(combinations(range(n),2))
 for bits in product([0,1],repeat=len(pairs)):
  E={p for p,b in zip(pairs,bits) if b}
  if not greedy(n,E):continue
  # Bound the stress test size. Include every order through n=3, and every
  # greedily ordered n=4 graph with at most two preceding nonneighbors.
  if n==4 and n-1-sum((h,n-1) in E for h in range(n-1))>2:continue
  r=analyze(n,E);counts['greedy_ordered_graphs']+=1;counts['unique_leading_checks']+=len(r)
  cases.append({'n':n,'edges':sorted(E),'checked_pairs':len(r)})
# Hall's non-greedy four-vertex cancellation example: exact zero edge dot product.
bad=analyze(4,{(0,2),(0,3),(1,3)},d=2,expect=False)
assert next(q for q in bad if q['pair']==[0,3])['nonzero'] is False
result={'status':'PASS',**counts,'finite_scope':'All greedily ordered labeled graphs n<=3; n=4 with k_max<=2','nongreedy_cancellation_reproduced':True,'cases':cases}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
