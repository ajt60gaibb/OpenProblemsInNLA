"""Exact regression certificates. Run: python code/verify_exact.py [--full].
These finite checks supplement, but cannot replace, the written proofs.
"""
from __future__ import annotations
import argparse, datetime, itertools, json, random, time, traceback
from fractions import Fraction as F
from pathlib import Path
import sympy as sp
from nla_algorithms import *

OUT = Path(__file__).resolve().parents[1] / 'verification' / 'exact_results.json'


def verify_iv06():
    l, d1, d2 = sp.symbols('lambda d1 d2')
    A = sp.Matrix([[25, -91+d1, 84+d2], [1, -1, 0], [1, 0, 1]])
    expected = (l-25)*(l*l+6)-d1*(l-1)-d2*(l+1)
    assert sp.expand((l*sp.eye(3)-A).det()-expected) == 0
    witnesses = [(-3,-21,154,[-4,2,1]), (0,-16,9,[-1,-1,1]),
                 (3,-146,29,[4,1,2]), (25,-91,84,[312,12,13])]
    for lam,a,b,v in witnesses:
        assert -166 <= a <= -16 and 9 <= b <= 159
        M = sp.Matrix([[25,a,b],[1,-1,0],[1,0,1]])
        assert M*sp.Matrix(v) == lam*sp.Matrix(v)
    gaps = []
    for lam, target in [(-1,(-332,-32)),(1,(-318,-18)),(12,(-3750,-150))]:
        c = (lam-25)*(lam*lam+6)
        r = 75*(abs(lam-1)+abs(lam+1))
        interval = (c-r,c+r)
        assert interval == target and interval[1] < 0
        gaps.append({'lambda':lam,'determinant_interval':interval})
    return {'status':'passed','integer_eigenpairs':4,'excluded_separators':gaps}


def fraction_endpoint_determinant(weights, gates):
    W = sum(weights); delta = F(1, 10*W*W)
    x,y = F(1),F(0)
    for i,w in enumerate(weights):
        t=delta*w; c=(1-t*t)/(1+t*t); s=2*t/(1+t*t)
        x,y = c*x-s*y, s*x+c*y
        if i < len(weights)-1:
            y = -gates[i]*y
    return x


def verify_partition(full):
    rng = random.Random(21140911)
    cases = [[1],[1,1],[1,2],[1,2,3],[1,2,4],[2,3,4,5],
             [1,1,1,1,1],[2,2,3,5,6],[1048576,1048577],
             [99991,100003,200002,100010]]
    cases += [[rng.randrange(1,40) for _ in range(m)]
              for m in range(2,9) for _ in range(60 if full else 4)]
    matrix_checks=0; endpoint_count=0
    for case_index, weights in enumerate(cases):
        W=sum(weights); delta=F(1,10*W*W); threshold=1-delta*delta/2
        partition = any(sum(s*w for s,w in zip(ss,weights)) == 0
                        for ss in signs(len(weights)))
        vals=[]
        for gates in signs(len(weights)-1):
            value=fraction_endpoint_determinant(weights,gates)
            assert value > 0
            vals.append(value); endpoint_count += 1
            if len(weights)<=3 and case_index<10:
                T,_,tau,_=partition_tridiagonal(weights,gates)
                assert continuant(T) == sp.Rational(value.numerator,value.denominator)
                assert T.det() == continuant(T)
                rhs=sp.zeros(T.rows,1); rhs[-1]=-1
                assert (T.inv()*rhs)[0] == 1/T.det()
                matrix_checks += 1
        assert (max(vals) >= threshold) == partition, weights
    return {'status':'passed','partition_instances':len(cases),
            'exact_gate_vertices':endpoint_count,'matrix_and_cofactor_checks':matrix_checks}


def verify_av02(full):
    rng=random.Random(2026091102)
    graph_count=0; threshold_count=0; inverse_checks=0; certificate_checks=0
    for v in range(2,10 if full else 6):
        for trial in range(20 if full else 4):
            edges=[(p,q) for p in range(v) for q in range(p+1,v)
                   if rng.random()<.45]
            if not edges: edges=[(0,1)]
            m=len(edges); N=1+v+m; a=96*N**4; rem=36*N**3
            cuts=[(sum(ss[p]!=ss[q] for p,q in edges),ss) for ss in signs(v)]
            C,ss=max(cuts)
            for k in range(1,m+1):
                q=isqrt(144*N*N*k); t=8*N**3*q
                assert t*t <= a*a*k
                assert t>rem and (t-rem)**2 > a*a*(k-1)
                threshold_count += 1
            if N<=14 and trial<3:
                A,t,B,K=maxcut_matrix(v,edges,C)
                ds=[1]+list(ss)+[1]*m
                M=A-sp.diag(*ds); Z=M.inv()
                X=sp.diag(*[sp.Rational(1,2-s) for s in ss])
                expected=sp.eye(N)
                expected[1:1+v,1:1+v]=X
                expected[0,1:1+v]=-K*sp.ones(1,v)*X
                expected[1:1+v,1+v:N]=-K*X*B
                expected[0,1+v:N]=K*K*sp.ones(1,v)*X*B
                assert Z==expected
                assert sum(z*z for z in Z[0,1+v:N]) == sp.Rational(4,9)*K**4*C
                assert inverse_norm_certificate_exact(A,t,ds)
                inverse_checks+=1; certificate_checks+=1
            graph_count += 1
    return {'status':'passed','graphs':graph_count,'integer_gap_checks':threshold_count,
            'exact_block_inverse_checks':inverse_checks,'exact_NP_certificates':certificate_checks}


def random_inverse_m_box(rng,n,k,width_denominator=100):
    M=sp.zeros(n)
    for i in range(n):
        for j in range(n):
            if i!=j: M[i,j]=-rng.randrange(1,5)
        M[i,i]=sum(-M[i,j] for j in range(n) if i!=j)+rng.randrange(2,6)
    C=M.inv(); R=sp.zeros(n)
    for i,j in rng.sample([(i,j) for i in range(n) for j in range(n)],min(k,n*n)):
        R[i,j]=C[i,j]*sp.Rational(rng.randrange(1,9),width_denominator)
    return C,R


def verify_iv03(full):
    rng=random.Random(2026091103)
    count=0; vertices=0
    endpoint_pairs=[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]
    # Exhaust all 1,296 2x2 boxes with endpoints in {0,1,2}.
    selections=itertools.product(endpoint_pairs,repeat=4)
    for pp in selections:
        L=sp.Matrix(2,2,[p[0] for p in pp]); U=sp.Matrix(2,2,[p[1] for p in pp])
        C=(L+U)/2; R=(U-L)/2
        got=inverse_m_vertices_exact(C,R)
        truth=True
        for A in entry_vertices(C,R):
            vertices+=1
            if not inverse_m_exact(A): truth=False; break
        assert got==truth
        count+=1
    for n in [3,4]:
        for t in range(30 if full else 5):
            C,R=random_inverse_m_box(rng,n,4,width_denominator=rng.choice([5,10,30,100]))
            got=inverse_m_vertices_exact(C,R)
            truth=True
            for A in entry_vertices(C,R):
                vertices+=1
                if not inverse_m_exact(A): truth=False; break
            assert got==truth
            count+=1
    # The adjugate completion lemma really requires n>=3.
    B=sp.Matrix([[1,2],[2,1]])
    assert B.det()<0 and B.adjugate()[0,1]<0
    return {'status':'passed','rational_boxes':count,'entry_vertices_checked':vertices,
            'all_2x2_endpoint_boxes_in_0_1_2':1296}


def ave_root_exact(C,R,sigma,b):
    n=C.rows; roots=set()
    D=sp.diag(*sigma)
    for ss in signs(n):
        J=C-D*R*sp.diag(*ss)
        x=J.inv()*b
        if all(ss[i]*x[i]>=0 for i in range(n)):
            roots.add(tuple(x))
    assert len(roots)==1, roots
    return sp.Matrix(next(iter(roots)))


def certify_lp(C,R,sigma,b,x):
    n=C.rows; D=sp.diag(*sigma)
    P,Q=C-D*R,C+D*R; X,Y=Q.inv(),P.inv()
    u=sp.Matrix([max(v,0) for v in x]); v=sp.Matrix([max(-v,0) for v in x])
    y=Q*v; G=X.col_join(Y); h=sp.zeros(n,1).col_join(-Y*b)
    assert X*y==v and Y*(y+b)==u
    assert all(a>=0 for a in G*y-h)
    active=[i for i,a in enumerate(G*y-h) if a==0]
    for rows in itertools.combinations(active,n):
        J=G[list(rows),:]
        if J.det()==0: continue
        lam=J.T.inv()*sp.ones(n,1)
        if all(z>=0 for z in lam):
            dual=sp.zeros(2*n,1)
            for row,z in zip(rows,lam): dual[row]=z
            assert G.T*dual==sp.ones(n,1)
            assert (h.T*dual)[0]==sum(y)
            return
    raise AssertionError('No exact primal/dual optimum certificate found')


def verify_iv05(full):
    rng=random.Random(2026091105)
    boxes=0; lp_certificates=0; vertices=0
    for n, trials in [(1,5),(2,10),(3,10),(4,5)]:
        if full: trials*=2
        for trial in range(trials):
            C,R=random_inverse_m_box(rng,n,4,width_denominator=200)
            matrices=list(entry_vertices(C,R))
            assert all(inverse_m_exact(A) for A in matrices)
            inverses=[A.inv() for A in matrices]
            bc=sp.Matrix([rng.randrange(-6,7) for _ in range(n)])
            br=sp.Matrix([rng.randrange(0,4) for _ in range(n)])
            if trial==0: bc=sp.zeros(n,1); br=sp.zeros(n,1)
            for i in range(n):
                for direction in [1,-1]:
                    sigma=[direction if j==i else -direction for j in range(n)]
                    b=bc+sp.diag(*sigma)*br
                    x=ave_root_exact(C,R,sigma,b)
                    certify_lp(C,R,sigma,b,x)
                    possible=[(B*b)[i] for B in inverses]
                    expected=max(possible) if direction==1 else min(possible)
                    assert x[i]==expected
                    lp_certificates+=1
            boxes+=1; vertices+=len(matrices)
    return {'status':'passed','rational_boxes':boxes,'exact_primal_dual_LP_certificates':lp_certificates,
            'exhaustive_matrix_vertices':vertices}


def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--full',action='store_true')
    args=parser.parse_args()
    result={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'mode':'full' if args.full else 'standard',
            'arithmetic':'Exact integers, fractions, and SymPy rationals',
            'finite_tests_are_not_a_proof':True}
    start=time.monotonic()
    try:
        for key,fn in [('IV-06',lambda:verify_iv06()),
                       ('IV-02_IV-04',lambda:verify_partition(args.full)),
                       ('AV-02',lambda:verify_av02(args.full)),
                       ('IV-03',lambda:verify_iv03(args.full)),
                       ('IV-05',lambda:verify_iv05(args.full))]:
            result[key]=fn(); OUT.write_text(json.dumps(result,indent=2)); print(key,result[key],flush=True)
        result['status']='passed'
    except Exception:
        result['status']='failed'; result['traceback']=traceback.format_exc()
        raise
    finally:
        result['elapsed_seconds']=time.monotonic()-start
        result['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
        OUT.write_text(json.dumps(result,indent=2))

if __name__=='__main__': main()
