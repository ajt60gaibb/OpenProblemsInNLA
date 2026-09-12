"""Deterministic numerical sanity checks; not a proof or certified norm bound."""
import numpy as np
from pathlib import Path
import hashlib,json
out=[]
for m,alpha in [(5,.2),(15,.4),(31,.499)]:
    h=2*np.pi/m; a=h*np.arange(m)
    s=alpha*np.array([(-1 if j%3==0 else (1 if j%3==1 else .3)) for j in range(m)])
    roots=np.exp(1j*(a+h*s));theta=h*np.sum(s)/2
    def P(z):return np.prod(z-roots)
    def R(z):return -np.exp(-1j*theta)*P(z)/(z**m+1)
    deriv=np.array([np.prod(roots[j]-np.delete(roots,j)) for j in range(m)])
    beta=np.cos(np.pi*s)/np.abs(deriv)
    imag=(1/R(0)).imag
    errmass=abs(np.sum(beta)-np.cos(theta))
    errrep=0.;errE=0.
    for z in [.3+.2j,-.5+.1j,.9*np.exp(.4j)]:
        f=1j*imag+np.sum(beta*(roots+z)/(roots-z))
        errrep=max(errrep,abs(f-1/R(z)))
        assert R(z).real>0
    N=(m-1)//2;nu=np.arange(-N,N+1)
    F=np.exp(1j*np.outer(a+h*s,nu))/np.sqrt(m)
    F0=np.exp(1j*np.outer(a,nu))/np.sqrt(m)
    E=F0@np.linalg.inv(F)
    for k in range(m):
        z=np.exp(1j*a[k])
        for j in range(m):
            ell=np.prod(z-np.delete(roots,j))/deriv[j]*np.exp(-1j*N*(a[k]-(a[j]+h*s[j])))
            errE=max(errE,abs(E[k,j]-ell))
    assert max(errmass,errrep,errE)<1e-10
    out.append({'m':m,'alpha':alpha,'mass_identity_error':errmass,'positive_real_representation_error':errrep,'Fourier_to_cardinal_identity_error':errE})
p=Path(__file__)
record={'status':'PASS numerical sanity only; all-stage proof is analytic','script_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'cases':out}
p.with_name('identity-checks.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
