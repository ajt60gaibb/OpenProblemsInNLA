import json,itertools
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1] / 'submitted'
def rref(a,p,n):
 a=[list(x) for x in a]; piv=[]
 for j in range(n):
  i=next((i for i in range(len(piv),len(a)) if a[i][j]%p),None)
  if i is None: continue
  k=len(piv);a[k],a[i]=a[i],a[k];inv=pow(a[k][j]%p,-1,p);a[k]=[v*inv%p for v in a[k]]
  for i in range(len(a)):
   if i!=k:
    z=a[i][j]%p
    if z:a[i]=[(x-z*y)%p for x,y in zip(a[i],a[k])]
  piv.append(j)
  if len(piv)==len(a):break
 return a[:len(piv)],piv
def check(n,p,index):
 cyc=json.loads((ROOT/f'data/patterns_n{n}.json').read_text())[index]['cycle']
 root=next(r for r in range(2,p) if pow(r,n,p)==1 and all(pow(r,k,p)!=1 for k in range(1,n)))
 t=[pow(root,j,p) for j in range(n)];pairs=list(itertools.combinations(range(3,n),2));pid={q:j for j,q in enumerate(pairs)}
 rows=[]
 for f in range(8):
  incidence=[j for j,m in enumerate(cyc) if m>>f&1]
  for five in itertools.combinations(incidence,5):
   row=[0]*len(pairs)
   for u,v in itertools.combinations(range(5),2):
    pair=(five[u],five[v])
    if pair not in pid:continue
    a,b,c=[t[five[k]] for k in range(5) if k not in (u,v)]
    row[pid[pair]]=(-1)**(u+v+1)*(b-a)*(c-a)*(c-b)*pow(a*b*c%p,-1,p)%p
   rows.append(row)
 rr,piv=rref(rows,p,len(pairs));free=[j for j in range(len(pairs)) if j not in piv];ell=len(free)
 b=[[0]*ell for _ in pairs]
 for k,j in enumerate(free):
  b[j][k]=1
  for row,i in zip(rr,piv):b[i][k]=-row[j]%p
 qr=[]
 for a,c,d,e in itertools.combinations(range(3,n),4):
  factors=[(pid[a,c],pid[d,e],1),(pid[a,d],pid[c,e],-1),(pid[a,e],pid[c,d],1)]
  qr.append([sum(sign*(b[i][u]*b[j][v]+(b[i][v]*b[j][u] if u!=v else 0)) for i,j,sign in factors)%p for u in range(ell) for v in range(u,ell)])
 rank=len(rref(qr,p,ell*(ell+1)//2)[1]);s=sum(a^b==255 for a,b in itertools.combinations(cyc,2));target=ell*(ell+1)//2-s
 assert rank==target,(n,index,ell,rank,target)
 return dict(n=n,prime=p,primitive_root=root,pattern=index,nullity=ell,complements=s,quadratic_rank=rank,target=target,passed=True)
records=[]
for n,p,indices in [(17,103,[0,1109,3073,6146]),(18,109,[0,224,448]),(19,191,list(range(14)))]:
 for index in indices:
  r=check(n,p,index);records.append(r);print(json.dumps(r),flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(records,indent=2)+'\n')
