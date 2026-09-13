from itertools import product
from math import comb
import json
import sympy as s

x=s.symbols('x')
Q=s.Rational
reports={}
# Reconstruct local derivative decompositions using rational nodes, avoiding
# the submission's root-of-unity and finite-field implementations entirely.
nodes=list(map(Q,[1,2,3,6]))+[Q(-1,2)]
P=s.Poly(s.prod(x-a for a in nodes),x)
assert P.nth(1)==0
weights=[]
for a in nodes:
    weights.append(s.Poly(s.cancel(P.as_expr()/((x-a)*P.diff().eval(a))),x).nth(1))
assert all(sum(w*a**d for w,a in zip(weights,nodes))==int(d==1) for d in range(6))

def basis(vectors):
    if not vectors: return []
    return s.Matrix.hstack(*vectors).columnspace()

def graph_case(alphas):
    # A is a product of dual numbers at double nodes and scalars at simple nodes.
    # Each pair (alpha, length) labels one local factor.
    factors=[]; ws=[]
    for alpha,ell in alphas:
        if ell==1:
            factors.append(s.Matrix([1,alpha,alpha**2]));ws.append(s.Integer(1))
        else:
            for a,w in zip(nodes,weights):
                factors.append(s.Matrix([1,alpha+a,alpha**2+2*alpha*a]));ws.append(w)
    r=sum(e for a,e in alphas);R=len(factors);N=r+R
    def mul(v,w):
        out=[];i=0
        for a,e in alphas:
            if e==1:out.append(v[i]*w[i]);i+=1
            else:out.extend([v[i]*w[i],v[i]*w[i+1]+v[i+1]*w[i]]);i+=2
        out.extend(v[j]*w[j] for j in range(r,N))
        return s.Matrix(out)
    U=[]
    for d in range(3):
        vals=[]
        for a,e in alphas:
            vals.append(a**d)
            if e==2:vals.append(d*a**(d-1) if d else 0)
        U.append(s.Matrix(vals+[v[d] for v in factors]))
    lam=[]
    for a,e in alphas:lam.extend([1] if e==1 else [0,1])
    lam=s.Matrix(lam+[-w for w in ws])
    W=U;dims=[len(W)];prefix=[]
    for j in range(2,6):
        W=basis([mul(v,u) for v in W for u in U]);dims.append(len(W));prefix.append(W)
    M=s.Matrix.hstack(*W)
    assert lam.T*M==s.zeros(1,M.cols)
    assert M[r:,:].rank()==R
    assert s.Matrix.hstack(*prefix[-2])[:r,:].rank()==r
    perp=M.T.nullspace();E=s.eye(N)
    equations=[]
    for v in W:
        mv=s.Matrix.hstack(*[mul(v,E[:,i]) for i in range(N)])
        equations.extend((o.T*mv).tolist()[0] for o in perp)
    K=s.Matrix(equations).nullspace()
    # Nilradical is span of epsilon coordinates. Intersect with K exactly.
    nil=[];i=0
    for a,e in alphas:
        if e==2:nil.append(E[:,i+1])
        i+=e
    assert len(K)+len(nil)-s.Matrix.hstack(*(K+nil)).rank()==0
    # All 3^5 tensor entries are checked independently of graph linear algebra.
    h=[sum((a**d if e==1 else (d*a**(d-1) if d else 0)) for a,e in alphas) for d in range(11)]
    for ids in product(range(3),repeat=5):
        assert sum(w*s.prod(v[i] for i in ids) for w,v in zip(ws,factors))==h[sum(ids)]
    return dict(local_factors=alphas,ordinary_terms=R,product_dimensions=dims,
                stabilizer_dimension=len(K),nilpotent_intersection_dimension=0,
                decomposition_coordinate_rank=R,entries_checked=3**5)
reports['rational_graphs']=[graph_case([(0,2),(1,1),(2,1)]),graph_case([(0,2),(1,2)])]
print(json.dumps(reports),flush=True)
# Test the stated Koszul identity coefficient by coefficient over Q, and its
# exact rank on arbitrary signed rational moments, including q=1 duplications.
Kreports=[]
for m,n in [(3,2),(3,3),(3,4),(5,2),(5,4),(7,3)]:
    q=n-1;k=(m-1)//2;a=k*q+1;b=q//2;c=q-b
    d1=a+b;d2=a+c;D=m*q
    E=s.zeros(3*a,d1+d2)
    for i in range(a):
        E[i,i+b]=1;E[a+i,i]=-1;E[a+i,d1+i+c]=1;E[2*a+i,d1+i]=-1
    assert E.rank()==d1+d2
    def mats(h):
        C=s.Matrix(d1,d2,lambda i,j:h[i+j]);Z=s.zeros(a)
        M=lambda sh:s.Matrix(a,a,lambda i,j:h[i+j+sh])
        K=s.BlockMatrix([[Z,M(q),-M(b)],[-M(q),Z,M(0)],[M(b),-M(0),Z]]).as_explicit()
        J=s.zeros(d1+d2);J[:d1,d1:]=C;J[d1:,:d1]=-C.T
        return C,K,J
    for pos in range(D+1):
        h=[s.Integer(i==pos) for i in range(D+1)]
        C,K,J=mats(h);assert K==E*J*E.T
    h=[Q((-1)**i*(i*i+2),(i%3)+1) for i in range(D+1)]
    C,K,J=mats(h);assert K.rank()==2*C.rank()
    Kreports.append(dict(m=m,n=n,basis_identities=D+1,middle_rank=C.rank(),koszul_rank=K.rank()))
reports['koszul']=Kreports
open('/private/tmp/nla-pr189-independent-check.json','w').write(json.dumps(reports,indent=2)+'\n')
print('PASS',json.dumps(reports),flush=True)
