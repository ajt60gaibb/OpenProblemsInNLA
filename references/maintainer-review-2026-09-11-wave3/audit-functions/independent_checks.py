"""Independent exact checks for PR110; no submission-code imports.

These are corroboration of the reviewed analytic proofs, not finite substitutes
for claims about all matrix families, all exponents or all switching lengths.
"""
from pathlib import Path
from fractions import Fraction as F
import itertools, json, math, random
import sympy as s

OUT=Path(__file__).resolve().parent
def matmul(a,b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),F(0))
             for j in range(len(b[0]))] for i in range(len(a))]

def main():
    report={}
    # Arbitrary complex lower-block entries, independent positive scale choices.
    exact_damping=0
    for d in range(1,7):
        for bits in itertools.product((0,1),repeat=d-1):
            ids=[0]
            for bit in bits:ids.append(ids[-1]+bit)
            b=ids[-1]+1
            hs=[s.Rational(2)**(b-j-1)*s.Rational(3)**((b-j-1)//2) for j in range(b)]
            x=s.Matrix(d,d,lambda i,j:s.Rational((i+1)*(j+2),i+j+1)+s.I*(i-j) if ids[i]>=ids[j] else 0)
            h=s.diag(*[hs[j] for j in ids]);y=x
            for cut in range(b-1):
                t=hs[cut+1]/hs[cut]
                sign=s.diag(*[1 if j<=cut else -1 for j in ids])
                y=(1+t)*y/2+(1-t)*sign*y*sign/2
            assert y == h*x*h.inv()
            # Damping the entire product equals multiplying the conjugated factors.
            z=2*x+s.eye(d) # another same-pattern matrix
            assert (h*(x*z)*h.inv()-(h*x*h.inv())*(h*z*h.inv())).applyfunc(s.expand)==s.zeros(d)
            exact_damping+=1
    report['exact_complex_block_damping_patterns']=exact_damping
    # Sharpness and endpoint claims are exact polynomial identities.
    z,delta=s.symbols('z delta')
    for d in range(1,11):
        N=s.zeros(d)
        for i in range(d-1):N[i,i+1]=1
        E=s.zeros(d);E[d-1,0]=delta
        assert s.expand((N+E).charpoly(z).as_expr()-(z**d-delta))==0
        J=s.eye(d)+N
        for n in range(1,16):
            assert J**n == sum((s.binomial(n,j)*N**j for j in range(d)),s.zeros(d))
    report['cyclic_sharpness_dimensions']=list(range(1,11))
    report['Jordan_power_identities']=150
    # Symbolic-q induction followed by compression proves the displayed identity.
    q=s.symbols('q',integer=True,nonnegative=True)
    lam,mu,t=s.symbols('lambda mu t',positive=True)
    jt=t*s.Matrix([[1,1],[0,1]])
    cand=t**q*s.Matrix([[1,q],[0,1]])
    assert cand.subs(q,0)==s.eye(2)
    assert s.simplify(jt*cand-cand.subs(q,q+1))==s.zeros(2)
    U=s.Matrix([[1,-1,0,1,0,0],[0,0,0,0,0,1]])
    V=s.Matrix([[1,0],[0,0],[1,0],[0,0],[0,1],[0,1]])
    assert U*V==s.eye(2) and (V*U)**2==V*U
    assert U*U.T==s.diag(3,1) and V.T*V==2*s.eye(2)
    aq=s.diag(1,cand.subs(t,lam),cand.subs(t,mu),1)
    assert s.simplify(U*aq*V-s.Matrix([[1-q*lam**q,q*mu**q],[0,1]]))==s.zeros(2)
    report['symbolic_compression_and_Gram_identities']=True
    # Rational exponent a/b: raise the budget inequality to b; no root rounding.
    gap_count=0; boundary_count=0;rng=random.Random(1100911)
    fractions=sorted({F(a,b) for b in range(2,9) for a in range(1,b)})
    for alpha in fractions:
        a,b=alpha.numerator,alpha.denominator
        lam,mu=F(1,2**b),F(1,2**(b-a))
        lists=[tuple(rng.randrange(0,15) for _ in range(rng.randrange(0,15))) for _ in range(100)]
        lists+=list(itertools.product(range(4),repeat=3))
        for qs in lists:
            prod=[[F(1),F(0)],[F(0),F(1)]]
            for qi in qs:
                loss=qi*lam**qi;gain=qi*mu**qi
                assert gain**b == F(qi)**a*loss**(b-a)
                prod=matmul([[1-loss,gain],[F(0),F(1)]],prod)
            weights=[math.prod((1-qj*lam**qj for qj in qs[i+1:]),start=F(1)) for i in range(len(qs))]
            assert sum((qi*lam**qi*w for qi,w in zip(qs,weights)),F(0))==1-prod[0][0]
            assert prod[0][1]**b <= sum(qs)**a
            assert 0<=prod[0][0]<=1
            gap_count+=1
        # Exact floor at both sides of breakpoints, up to hundreds of digits.
        for j in [1,2,3,4,10,30,100]:
            threshold=2**(b*j)
            for n in [threshold-1,threshold,threshold+1,2*threshold-1]:
                q=(n.bit_length()-1)//b
                if not q:
                    assert n < 1/lam
                    continue
                assert lam**(-q)<=n<lam**(-(q+1))
                k,r=divmod(n,q+1)
                assert k*(q+1)+r==n and 0<=r<q+1
                assert n>=2*(q+1) and k>=F(n,2*(q+1))
                assert k*q*lam**q>=F(1,4)
                assert lam**(-q)>=lam*n
                boundary_count+=1
    report['rational_exponents']=list(map(str,fractions))
    report['exact_arbitrary_gap_budget_checks']=gap_count
    report['exact_lower_word_boundary_checks']=boundary_count
    report['status']='PASS; finite exact corroboration, universal proofs separately reviewed'
    (OUT/'independent-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
