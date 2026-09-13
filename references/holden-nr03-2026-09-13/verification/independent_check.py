import csv, hashlib, json, math
from pathlib import Path
root=Path(__file__).resolve().parents[1]
c=json.loads((root/'data/factors_n7.json').read_text())
W,V,d=c['W'],c['H_scaled'],c['denominators']
assert c['n']==7 and c['r']==127
assert len(W)==128 and all(len(row)==127 for row in W)
assert len(V)==127 and all(len(row)==128 for row in V)
assert len(d)==128 and all(type(x) is int and x>0 for x in d)
assert all(type(x) is int and x>=0 for row in W+V for x in row)
zeros=0
for a in range(128):
 for b in range(128):
  t=len(set(i for i in range(7) if a//(2**i)%2) & set(i for i in range(7) if b//(2**i)%2))
  expected=(1-t)**2*d[b]
  actual=sum(W[a][k]*V[k][b] for k in range(127))
  assert expected==actual,(a,b,expected,actual)
  zeros+=t==1
# Separate direct set construction of the four families for n<=7.
from itertools import combinations
for n in range(1,8):
 universe=frozenset(range(n))
 sets=[frozenset(i for i in range(n) if a//2**i%2) for a in range(2**n)]
 reps=[s for s in sets if n-1 not in s]
 pairs=list(map(frozenset,combinations(range(n),2)))
 fours=list(map(frozenset,combinations(range(n),4)))
 for a in sets:
  for b in sets:
   p=len(b); t=len(a&b)
   g=sum((1-len(s&b))**2*(1-len((universe-s)&b))**2 for s in reps if a in (s,universe-s))
   e=sum(int(i not in a and b==frozenset([i])) for i in range(n))
   pair=sum(4*(p-2) for s in pairs if s<=a and s<=b)
   four=sum(12*max(len(a&s)-2,0) for s in fours if s<=b)
   assert min(g,e,pair,four)>=0
   assert g+e+pair+four==max(1,(p-1)**2)*(1-t)**2
 print('PASS independent set-based family reconstruction n=',n)
print('PASS stored certificate: 16384 entries; zero count',zeros,'rank bound 127<128')
for name in ['NR03_counterexample.tex','data/factors_n7.json']:
 print('SHA256',name,hashlib.sha256((root/name).read_bytes()).hexdigest())
