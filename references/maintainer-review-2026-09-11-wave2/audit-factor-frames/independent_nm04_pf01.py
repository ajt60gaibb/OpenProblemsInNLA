"""Fresh exact constructions for NM04 and PF01; no submitted code imported."""
from pathlib import Path
import itertools as it
import json
import sympy as s
checks={}
def ck(name,b):checks[name]=bool(b);assert b,name
def sets(m,n):
    return [(R,C) for k in range(min(m,n)) for R in it.combinations(range(1,m),k) for C in it.combinations(range(1,n),k)]
def det(A,R,C):return A.extract(R,C).det()
def pos(seq,x):return seq.index(x)+1
for m,n in [(1,1),(1,3),(3,1),(2,3),(3,2),(3,3),(4,3)]:
    # Any positive rational input is already balanced for its own margins.
    A=s.Matrix(m,n,lambda i,j:s.Rational(1+((int(i)+2)*(int(j)+3))%11,13))
    r=list(A*s.ones(n,1));c=list((s.ones(1,m)*A).T);total=sum(r);x=A[0,0]
    D=sets(m,n);G=s.zeros(len(D));Delta=[];Gamma=[]
    for i,(R,C) in enumerate(D):
        Delta.append(det(A,(0,)+R,(0,)+C));Gamma.append(x*det(A,R,C))
        for j,(U,V) in enumerate(D):
            rm=set(R)-set(U);ra=set(U)-set(R);cm=set(C)-set(V);ca=set(V)-set(C)
            if i==j:G[i,j]=sum(r[k] for k in R)+sum(c[k] for k in C)-total
            elif not rm and not cm and len(ra)==len(ca)==1:
                u=next(iter(ra));v=next(iter(ca));G[i,j]=(-1)**(pos(U,u)+pos(V,v))
            elif not ra and not ca and len(rm)==len(cm)==1:
                u=next(iter(rm));v=next(iter(cm));G[i,j]=-(-1)**(pos(R,u)+pos(C,v))*r[u]*c[v]
            elif not rm and not ra and len(cm)==len(ca)==1:
                u=next(iter(cm));v=next(iter(ca));G[i,j]=(-1)**(pos(C,u)+pos(V,v))*c[u]
            elif not cm and not ca and len(rm)==len(ra)==1:
                u=next(iter(rm));v=next(iter(ra));G[i,j]=(-1)**(pos(R,u)+pos(U,v))*r[u]
    K=s.diag(*Gamma)+x/(r[0]*c[0])*G*s.diag(*Delta)
    ck(f'weighted_null_{m}_{n}',K*s.ones(len(D),1)==s.zeros(len(D),1))
    if m+n==2:continue
    p=m-1;d=m+n-2
    uv=s.Matrix([-1]*p+c[1:]);vv=s.Matrix(r[1:]+[1]*(n-1));E=uv*vv.T
    S=[tuple([i for i in range(p) if i+1 not in R]+[p+j-1 for j in C]) for R,C in D]
    compound=s.zeros(len(D))
    for j,ind in enumerate(S):
        for place,old in enumerate(ind):
            for new in range(d):
                changed=list(ind);changed[place]=new
                if len(set(changed))<p:continue
                inv=sum(changed[k]>changed[l] for k in range(p) for l in range(k+1,p))
                i=S.index(tuple(sorted(changed)))
                compound[i,j]+=(-1)**inv*E[new,old]
    J=s.diag(*[(-1)**(sum(R)+(p+1)*len(R)+len(R)*(len(R)-1)//2) for R,C in D])
    ck(f'compound_identity_{m}_{n}',G==J*compound*J-r[0]*s.eye(len(D)))
    z=s.symbols('z');N1=s.binomial(m+n-3,m-2) if m>=2 else 0;N2=s.binomial(m+n-3,m-1)
    ck(f'characteristic_{m}_{n}',s.expand(G.charpoly(z).as_expr()-(z+c[0])**N1*(z+r[0])**N2)==0)

# Four derivative identities are universal polynomial identities. Independently
# pull back direct minor differentiation on a symbolic 3-by-3 matrix.
v=s.symbols('v:9');T=s.Matrix(3,3,v);one=s.ones(3,1)
directions=[one*one.T,(T*one)*one.T,one*(one.T*T),(T*one)*(one.T*T)]
for R,C in sets(4,4):
    R=tuple(i-1 for i in R);C=tuple(j-1 for j in C);k=len(R)
    f=det(T,R,C);der=[sum(s.diff(f,v[j])*Z[j] for j in range(9)) for Z in directions]
    L=sum((-1)**(pos(R,i)+pos(C,j))*det(T,tuple(a for a in R if a!=i),tuple(a for a in C if a!=j)) for i in R for j in C)
    U=sum((-1)**(pos(tuple(sorted(R+(i,))),i)+pos(tuple(sorted(C+(j,))),j))*det(T,tuple(sorted(R+(i,))),tuple(sorted(C+(j,)))) for i in range(3) if i not in R for j in range(3) if j not in C)
    CC=sum((-1)**(pos(C,i)+pos(tuple(sorted(tuple(a for a in C if a!=i)+(j,))),j))*det(T,R,tuple(sorted(tuple(a for a in C if a!=i)+(j,)))) for i in C for j in range(3) if j not in C)
    RR=sum((-1)**(pos(R,i)+pos(tuple(sorted(tuple(a for a in R if a!=i)+(j,))),j))*det(T,tuple(sorted(tuple(a for a in R if a!=i)+(j,))),C) for i in R for j in range(3) if j not in R)
    ck(f'four_minor_derivatives_{R}_{C}',all(s.expand(a-b)==0 for a,b in zip(der,[L,k*f+CC,k*f+RR,sum(T)*f-U])))

# Explicit size-four graph factors for both PF01 instances, including every
# interlayer trace, with radicals simplified exactly.
h=s.zeros(4,5)
for r in range(1,5):
    for i in range(r):h[r-1,i]=1/s.sqrt(r*(r+1))
    h[r-1,r]=-r/s.sqrt(r*(r+1))
points=[]
pairs=list(it.combinations(range(5),2))
for I in pairs:
    z=h*s.Matrix([int(i in I) for i in range(5)])/s.sqrt(2)
    points.append(s.Matrix(2,2,list(z)))
t=(3+s.sqrt(5))/2;aa=[];bb=[]
for layer in (0,1):
    for Z in points:
        C=Z.col_join(s.eye(2)) if layer==0 else (-Z).col_join(t*s.eye(2))
        F=s.eye(2).col_join(-Z.T) if layer==0 else s.eye(2).col_join(Z.T/t)
        aa.append(C*C.T/(1 if layer==0 else t));bb.append(F*F.T*(1 if layer==0 else t))
for i,j in it.product(range(20),repeat=2):
    d=2-len(set(pairs[i%10])&set(pairs[j%10]));want=d if i//10==j//10 else 3-d
    ck(f'pf01_graph_trace_{i}_{j}',s.simplify(s.trace(aa[i]*bb[j]))==want)
out={'passed':sum(checks.values()),'total':len(checks),'checks':checks}
(Path(__file__).parent/'nm04-pf01-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'{out["passed"]}/{out["total"]} exact checks passed')
