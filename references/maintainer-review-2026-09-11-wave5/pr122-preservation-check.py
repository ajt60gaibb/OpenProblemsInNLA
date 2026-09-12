'''Independent NumPy diagnostic for the proof's simultaneous-preservation step.'''
import numpy as np,json
rng=np.random.default_rng(122)
def coefnorm(p):return np.linalg.norm(p)
def mul(p,q):return np.convolve(p,q)
def to_matrix(p,n):
 M=np.zeros((n,n),complex)
 for j in range(n):
  for i in range(j,n):M[i,j]=p[i-j]
 return M

def circle_coeff(h,m):
 result=np.zeros(2*m+1,complex)
 for i in range(len(h)):
  for j in range(len(h)):result[i-j+m]+=h[i]*h[j].conjugate()
 return result
records=[];largest_moment_error=0.;largest_factor_error=0.
for n in range(2,10):
 for d in range(n):
  for trial in range(4):
   alphas=.6*rng.random(d)*np.exp(2j*np.pi*rng.random(d))
   if trial==1 and d:alphas[0]=0 # singular T, degree(b)<degree(a)
   if trial==2 and d>=2:alphas[1]=alphas[0] # repeated Blaschke root
   a=np.array([np.exp(2j*np.pi*rng.random())]);b=np.array([1.+0j])
   for alpha in alphas:
    a=mul(a,[-alpha,1]);b=mul(b,[1,-alpha.conjugate()])
   # Division of a by b in the truncated power-series ring.
   symbol=np.zeros(n,complex)
   for j in range(n):
    value=a[j] if j<len(a) else 0.
    for ell in range(1,min(j,len(b)-1)+1):value-=b[ell]*symbol[j-ell]
    symbol[j]=value/b[0]
   T=to_matrix(symbol,n);m=n-1-d
   assert abs(np.linalg.norm(T,2)-1)<1e-10
   hs=[rng.normal(size=m+1)+1j*rng.normal(size=m+1) for _ in range(4)]
   hs=[h/coefnorm(mul(b,h)) for h in hs]
   omega=rng.random(4);omega/=omega.sum()
   Q=sum(w*circle_coeff(h,m) for w,h in zip(omega,hs))
   if m==0:h=np.array([np.sqrt(Q[0].real)])
   else:
    roots=np.polynomial.polynomial.polyroots(Q)
    chosen=sorted(roots,key=abs)[:m]
    h=np.polynomial.polynomial.polyfromroots(chosen)
    h*=np.sqrt(Q[m].real/(coefnorm(h)**2))
   factor_error=float(np.linalg.norm(circle_coeff(h,m)-Q))
   largest_factor_error=max(largest_factor_error,factor_error)
   assert factor_error<1e-9
   f=mul(b,h);fs=[mul(b,x) for x in hs]
   assert len(f)<=n and abs(np.linalg.norm(f)-1)<1e-9
   f=np.pad(f,(0,n-len(f)));fs=[np.pad(x,(0,n-len(x))) for x in fs]
   assert np.linalg.norm(T@f-np.pad(mul(a,h),(0,n-len(mul(a,h)))))<1e-9
   # All n powers of the lower shift span every triangular Toeplitz direction.
   moment_error=0.
   for j in range(n):
    r=np.zeros(n,complex);r[j]=1;R=to_matrix(r,n)
    target=sum(w*np.vdot(T@x,R@x) for w,x in zip(omega,fs))
    actual=np.vdot(T@f,R@f)
    moment_error=max(moment_error,float(abs(actual-target)))
   largest_moment_error=max(largest_moment_error,moment_error)
   assert moment_error<1e-9
   records.append({'n':n,'Blaschke_degree':d,'trial':trial,'factor_error':factor_error,'maximum_complex_moment_error':moment_error})
# Explicit root-on-the-circle and zero/constant effective-degree cases.
unit=np.array([1.,-2.,1.]);assert np.allclose(circle_coeff(unit,2),[1,-4,6,-4,1])
assert np.allclose(circle_coeff(np.array([0.]),0),[0.])
assert np.allclose(circle_coeff(np.array([3j]),0),[9.])
print(json.dumps({'status':'PASS','cases':len(records),'maximum_factor_error':largest_factor_error,
'maximum_complex_moment_error':largest_moment_error,'unit_circle_and_constant_cases':'PASS','checks':records},indent=2))
