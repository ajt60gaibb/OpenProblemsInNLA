from mi15_gram import setup
from fractions import Fraction as F
from pathlib import Path
from math import lcm
import numpy as np
from scipy.linalg import solve_triangular
import json, argparse, time

def complement(pairs,n):
 groups=[];covered=set();columns=[]
 for k in range(n-1):
  g=[i for i,(a,b) in enumerate(pairs) if b-a==2*(n-1)-k]
  assert g
  groups.append(g);covered.update(g)
  for i in g[1:]:columns.append({i:1,g[0]:-1})
 for i in range(len(pairs)):
  if i not in covered:columns.append({i:1})
 return groups,columns

def certify(n,roundden=10**6,scale=10**9):
 start=time.time();root=Path(__file__).parent
 fl=np.load(root/f'mi15_n{n}_K{n-2}.npz')
 desc=json.loads((root/f'mi15_n{n}_K{n-2}.json').read_text())
 z=[F(round(float(x)*roundden),roundden) for x in fl['z']]
 t=[]
 for e in desc['expressions']:
  t.append(F(e['constant'])+sum((F(c)*z[int(b)] for b,c in e['coefficients'].items()),F(0)))
 vals,pairs,C,Qafter,zero,keep,free,forced,ii,jj,sg=setup(n)
 all_t=[(abcd,F(v)) for abcd,v in forced]+[(abcd,t[a]) for a,(abcd,_) in enumerate(free)]
 D=1
 for _,v in all_t:D=lcm(D,v.denominator)
 pd={p:i for i,p in enumerate(pairs)};d=len(pairs)
 base=2*np.diag([(n-abs(a))*(n-abs(b)) for a,b in pairs])-C.T@C
 Q=np.array(base,dtype=object)*D
 records=[]
 for (a,b,c,e),v in all_t:
  v=int(v*D)
  if not v:continue
  records.append([a,b,c,e,v])
  for p,q,s in [((a,b),(c,e),1),((a,c),(b,e),-1),((a,e),(b,c),1)]:
   i,j=pd[p],pd[q];Q[i,j]+=s*v;Q[j,i]+=s*v
 groups,cols=complement(pairs,n)
 for g in groups:
  assert all(sum(Q[i,j] for j in g)==0 for i in range(d)),('kernel failure',g)
 h=len(cols)
 G=np.empty((h,h),dtype=object)
 for i,ci in enumerate(cols):
  for j,cj in enumerate(cols):
   G[i,j]=sum(si*sj*Q[a,b] for a,si in ci.items() for b,sj in cj.items())
 Gfloat=np.asarray(G,dtype=float)/D
 L=np.linalg.cholesky(Gfloat)
 T=solve_triangular(L.T,np.eye(h),lower=False)
 Tint=np.array(np.rint(T*scale),dtype=object)
 Tint=np.array([[int(v) for v in row] for row in Tint],dtype=object)
 H=Tint.T@G@Tint
 margins=[H[i,i]-sum(abs(H[i,j]) for j in range(h) if j!=i) for i in range(h)]
 assert min(margins)>0, 'diagonal dominance failed'
 payload={'schema':'toeplitz-bw-sos-rational-v1','n':n,'gram_denominator':D,
  'plucker_coefficients':records,'congruence_denominator':scale,
  'congruence_numerators':Tint.tolist(),
  'integer_diagonal_dominance_minimum':str(min(margins)),
  'complement_dimension':h,
  'rounding_denominator_for_free_parameters':roundden,
  'note':'All polynomial identities, kernel identities, and diagonal-dominance inequalities are exact. Floating point used only for discovery.'}
 out=root/'mi15_certificates';out.mkdir(exist_ok=True)
 (out/f'n{n}.json').write_text(json.dumps(payload,separators=(',',':'))+'\n')
 print('CERTIFIED',n,'full d',d,'rank',h,'D',D,'positive integer margin',min(margins),'normalized margin',float(F(min(margins),D*scale*scale)),'sec',time.time()-start,flush=True)
 return payload

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('orders',nargs='*',type=int,default=[8,9,10,11,12]);args=ap.parse_args()
 for n in args.orders:certify(n)
