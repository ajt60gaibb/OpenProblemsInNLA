"""Independent exact checks for PRs 190 and 191; no submission code imported."""
import json
import random
from pathlib import Path
import sympy as s

x = s.symbols('x')
rng = random.Random(190191)
out = {}

# RA-14: exact noncommuting trace identity and Loewner majorization.
L1=s.diag(3,4,6)
L2=s.diag(-1,0,1, s.Rational(1,2))
F=s.Matrix(4,3,[s.Rational(rng.randint(-4,4),7) for _ in range(12)])
S=F.T*F
C=(s.eye(3)+S).inv()
actual=s.trace(L1)-s.trace((L1+F.T*L2*F)*C)
decomposed=s.trace((L1-3*s.eye(3))*S*C)+s.trace(F.T*(3*s.eye(4)-L2)*F*C)
weighted=sum((L1[i,i]-L2[j,j])*F[j,i]**2 for i in range(3) for j in range(4))
assert L1*S != S*L1
assert actual == decomposed and weighted >= actual >= 0
assert (S-S*C).is_positive_semidefinite
assert (s.eye(3)-C).is_positive_semidefinite
out['ra14_noncommuting_trace']={'identity':True,'exact_loss':str(actual),'exact_majorant':str(weighted)}

# RA-14: exact family of identical two-sided transcripts, including adaptive rows.
H=s.Matrix(7,4,[rng.randint(-5,5) for _ in range(28)])
c1=s.Matrix([1,2,-1,3]); x1=H*c1+s.Matrix([2,0,1,0,-1,1,0])
c2=H.T*x1+s.Matrix([1,-1,0,2])
CC=s.Matrix.hstack(c1,c2); XX=x1
PC=CC*(CC.T*CC).inv()*CC.T
PX=XX*(XX.T*XX).inv()*XX.T
mean=PX*H+H*PC-PX*H*PC
G=s.Matrix(7,4,[rng.randint(-7,7) for _ in range(28)])
completion=mean+(s.eye(7)-PX)*G*(s.eye(4)-PC)
assert completion*CC==H*CC and XX.T*completion==XX.T*H
assert H.rank()==completion.rank()==4
assert s.Matrix.hstack(H,completion).rank()>4
out['ra14_transcript_completion']={'same_queries_and_answers':True,'different_ranges':True,'queries':3,'rank':4}

# RA-14: exact constants and scalar polynomial properties, independent expansion.
cert=sum(s.Rational(10**(2*j),s.factorial(2*j)) for j in range(1,8))
assert cert==s.Rational(5860808350,567567) and cert>10000
assert s.Rational(25,2)*11**4<200000
for m in range(1,21):
    p=s.cancel((s.chebyshevt(m,x)-1)/(x-1))
    assert s.degree(p,x)==m-1 and p.subs(x,1)==m*m
    assert s.expand(p-m-2*sum((m-j)*s.chebyshevt(j,x) for j in range(1,m)))==0
out['ra14_fejer']={'degrees_checked':20,'exact_cosh_certificate':str(cert)}

def krylov(nodes,H,depth):
    return s.Matrix.hstack(*(s.diag(*nodes)**r*H for r in range(depth)))

def gap(nodes,b):
    return min((nodes[i]-nodes[i+b])/nodes[i] for i in range(len(nodes)-b)) if len(nodes)>b else s.Integer(1)

fixtures=[(2,4,[20,20,11,10,6,6,2,1]),
          (3,3,[100,99,99,20,20,19,1,s.Rational(99,100),s.Rational(49,50)]),
          (2,3,[10**12,10**12,2,2,s.Rational(1,10**6),s.Rational(1,10**6)])]
records=[]
for b,t,values in fixtures:
    nodes=list(map(s.Rational,values)); m=b*t; Delta=gap(nodes,b)
    sets=[]
    for i in range(m):
        near=[j for j in range(m) if (1-Delta/2)*nodes[i]<=nodes[j]<=(1+Delta/2)*nodes[i]]
        assert i in near and len(near)<=b
        near += [j for j in range(m) if j not in near][:b-len(near)]
        sets.append([j for j in range(m) if j not in near])
    for attempt in range(50):
        H=s.Matrix(m,b,[rng.randint(-9,9) for _ in range(m*b)])
        K=krylov(nodes,H,t)
        if K.det() and all(krylov([nodes[j] for j in S],H.extract(S,list(range(b))),t-1).det() for S in sets):
            break
    else:
        raise AssertionError('No nonsingular rational fixture')
    Ki=K.inv()
    E=s.Matrix.hstack(*(x**r*s.eye(b) for r in range(t)))*Ki
    for i,Sidx in enumerate(sets):
        # The normalized column need not have rational unit norm. Homogeneity
        # lets us check the exact identity before Euclidean normalization.
        P=E[:,i]; z=P.subs(x,nodes[i])
        assert z!=s.zeros(b,1)
        HS=H.extract(Sidx,list(range(b)))
        subnodes=[nodes[j] for j in Sidx]
        assert gap(subnodes,b)>=Delta
        KS=krylov(subnodes,HS,t-1)
        ES=s.Matrix.hstack(*(x**r*s.eye(b) for r in range(t-1)))*KS.inv()
        D=s.diag(*(1/(nodes[j]-nodes[i]) for j in Sidx))
        assert (P-z+(x-nodes[i])*ES*D*HS*z).applyfunc(s.cancel)==s.zeros(b,1)
        assert all((H[j,:]*P.subs(x,nodes[j]))[0]==int(j==i) for j in range(m))
    # Translation must preserve the interpolation evaluation, even at extreme scales.
    shift=nodes[-1]/3
    shifted=krylov([z-shift for z in nodes],H,t).inv()
    assert E.subs(x,shift)==shifted[:b,:]
    # Exact zero-tail recovery and nondivisible target support.
    T=s.Matrix(3,b,[rng.randint(-5,5) for _ in range(3*b)])
    G=H.col_join(T); allnodes=nodes+[s.Integer(0)]*3
    MG=s.diag(*allnodes)*G
    powered=krylov(allnodes,MG,t)
    assert powered[:m,:].rank()==m and powered[m:,:]==s.zeros(3,m)
    records.append({'b':b,'t':t,'gap':str(Delta),'recursive_columns':m,'translation':True,'exact_zero_tail_rank':m})
out['ra04_new_rational_fixtures']=records
out['all_passed']=True
Path('/private/tmp/nla-ra-independent-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
