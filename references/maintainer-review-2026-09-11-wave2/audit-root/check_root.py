"""Independent algebra/certificate diagnostics; not universal proof certificates."""
from pathlib import Path
import itertools, json
import numpy as np
import sympy as s

result = {}
k, p = s.symbols('k p', positive=True)
ss = p*(k+2)/(k+p)
assert s.simplify((1+2/k)*2/ss - (2/p+2/k)) == 0
assert s.simplify(1+(p-1)*(k-p)/(k+p)-ss*(k-p+2)/(k+2)) == 0
assert s.simplify((k+2)*ss/ss - (k+2)) == 0
result['MI28_exact_exponent_identities'] = 'PASS'
y = s.symbols('y1:4')
assert s.expand((y[0]+y[1]+y[2])-(y[1]+y[2])-y[2]) == y[0]-y[2]
z = s.symbols('z')
assert s.expand(3*(z**5-z**3+z)-(z**5+z**3+z)) == s.expand(2*z*(z*z-1)**2)
result['AA01_exact_examples'] = 'PASS'
t = s.symbols('t')
G = s.Matrix([[t+2,t-1],[t-1,t+2]])
F = s.Matrix([[t-1,t-1],[t+2,t-1]])
det = s.expand((z*G-F).det())
assert s.expand(det-3*((2*t+1)*z*z+(1-t)*z+(1-t))) == 0
assert s.expand(s.discriminant(det,z)-27*(t-1)*(3*t+1)) == 0
result['IE10_exact_pencil'] = str(s.factor(det))

rng = np.random.default_rng(20260911)
def power(A, q):
    w,V=np.linalg.eigh((A+A.conj().T)/2)
    assert min(w)>0
    return (V*w**q)@V.conj().T
mi_count=0
max_minor_violation=0.0
for n in [2,3,5]:
    for _ in range(12):
        X=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)); A=X.conj().T@X+np.eye(n)
        X=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)); B=X.conj().T@X+np.eye(n)
        D=power(B@A@A@B,.5)
        for kk,pp in [(0,0),(0,.1),(.05,.001),(.5,.2),(1.5,.2),(1.9,1.1),(2,2),(3,.3),(4,1.7)]:
            R=power(A,(pp-kk)/2); H=R@power(B,pp)@R
            R=power(A,-kk/2); Z=R@power(D,pp)@R
            lh=np.log(np.linalg.eigvalsh(H))[::-1]; lz=np.log(np.linalg.eigvalsh(Z))[::-1]
            diff=np.cumsum(lh-lz)
            max_minor_violation=max(max_minor_violation,float(max(diff)))
            assert max(diff)<1e-8 and abs(diff[-1])<1e-8
            mi_count+=1
result['MI28_numerical_diagnostics']={'pairs':mi_count,'largest_roundoff_violation':max_minor_violation}

ie_count=0
for n in range(3,15):
    nodes=np.exp(2j*np.pi*np.arange(n)/n)
    for kk in sorted(set([2,n-1])):
        for _ in range(3):
            w=np.exp(rng.normal(size=n))
            U=(w**.5)[:,None]*nodes[:,None]**np.arange(kk)[None,:]
            Q,_=np.linalg.qr(U); H=Q.conj().T@(nodes[:,None]*Q)
            ev,R=np.linalg.eig(H); R=R/np.linalg.norm(R,axis=0)
            dual=np.linalg.inv(R); conds=np.linalg.norm(dual,axis=1)
            assert np.linalg.cond(R@np.diag(np.sqrt(conds))) <= conds.sum()+1e-8
            for i,lam in enumerate(ev):
                r=Q@R[:,i]; ell=nodes**(kk-1)*r.conj(); alpha=np.vdot(ell,r)
                assert np.linalg.norm(H.conj().T@(Q.conj().T@ell)-lam.conjugate()*(Q.conj().T@ell))<1e-10
                assert abs(1/abs(alpha)-conds[i])<1e-7
                sensitivity=sum(abs((nodes-lam)*ell.conj()*r/alpha))
                d=min(abs(nodes[0]-nodes[1:]))
                assert conds[i] <= max(2,8*sensitivity/d)+1e-7
            ie_count+=1
result['IE10_numerical_diagnostics']={'compressions':ie_count,'checks':'antiunitary left vectors, projector norms, balanced eigenbasis and sensitivity'}

signs=[]
for pp in [13,17,19,23,29,37,43,101,367]:
    chi=np.zeros(pp,dtype=int)
    chi[1:]=[1 if pow(v,(pp-1)//2,pp)==1 else -1 for v in range(1,pp)]
    dd=next(v for v in range(1,pp) if chi[v]<0); eps=int(chi[-1])
    x,y=np.indices((pp,pp)); c=chi[(x*x-dd*y*y)%pp]; a=c.copy(); a[0,0]=eps
    S=[((2*dd*v)%pp,(1+dd*v*v)%pp) for v in range(1,pp) if chi[v]==1]
    assert len(set(S))==(pp-1)//2
    for u,v in S:
        assert c[u,v]==-eps
        a[u,v]+=2*eps
    assert set(np.unique(a))=={-1,1} and a.sum()==eps*pp
    fc=np.fft.fft2(c); fa=np.fft.fft2(a)
    expected=-eps*pp*chi[(x*x-pow(dd,-1,pp)*y*y)%pp]
    assert np.max(abs(fc-expected))<1e-8
    sv=abs(fa); err=2+3*np.sqrt(pp)
    assert sv.min()>=pp-err-1e-8 and sv.max()<=pp+err+1e-8
    signs.append({'prime':pp,'condition_number':float(sv.max()/sv.min()),'exact_sign_and_dc_checks':True})
result['IS04_family_diagnostics']=signs
assert 210**2 < 2*151**2
result['IS04_exact_threshold']='PASS'
out=Path(__file__).with_suffix('.json');out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
