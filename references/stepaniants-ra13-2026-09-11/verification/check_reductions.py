"""Exact algebra checks and limited probability sanity checks, not a proof audit."""
import math
import numpy as np
from fractions import Fraction as F
from scipy.integrate import quad
from scipy.special import gammaincc, gammaln

for a in [F(1,5),F(2,3),F(1)]:
 for b in [F(-1),F(-1,3),F(1,7)]:
  for l in [1,2,5]:
   alpha=F(1,2);s=F(2,5)
   log_derivative=alpha*((s-s/(1+a*s))*l/(2*a) + l*(s-s/(1+b*s))*(-1/(2*b)))
   claimed=l*alpha*(b-a)*s**3/(2*(1+a*s)*(1+b*s))
   assert log_derivative==claimed
print('Twenty-seven rational grouped-transform derivative checks: PASS')

# Shape five makes sqrt(R-1)=2 rational.
R=F(5)
for w in [F(1), F(-1), F(1,3),F(-2,3)]:
 d=-w+2*abs(w)
 assert d*d+2*d*w+2*w*w==R*w*w
print('Exact single-scale inflection identity, four signed scales at shape five: PASS')

def raw_survival(w,x):
 # Independent, distinct signed unit-shape Gamma scales; exact partial-fraction formula.
 c=[math.prod(wi/(wi-wj) for j,wj in enumerate(w) if j!=i) for i,wi in enumerate(w)]
 if x>=0:
  return sum(ci*math.exp(-x/wi) for ci,wi in zip(c,w) if wi>0)
 return 1-sum(ci*math.exp(-x/wi) for ci,wi in zip(c,w) if wi<0)

def extremal_survival(r,h):
 k=int(math.floor(r)); q=math.sqrt(r-k); x=h+k+q
 if q==0:return float(gammaincc(k,x))
 if k==0:return math.exp(-x/q)
 integrand=lambda y:0 if y==0 else math.exp((k-1)*math.log(y)-y-gammaln(k)-(x-y)/q)
 return float(gammaincc(k,x))+quad(integrand,0,x,epsabs=1e-12,epsrel=1e-12)[0]

for w in [[-1,.2,.5,.7],[-1,-.8,.3,.6],[-1,-.9,-.6,-.2],[1,.7,.4,.1],[1,-.9,.8,-.7,.6,-.5]]:
 r=sum(t*t for t in w);H=1+math.sqrt(r+1)
 for factor in [1,1.5,2]:
  h=factor*H; upper=raw_survival(w,h+sum(w)); lower=1-raw_survival(w,-h+sum(w))
  ext=extremal_survival(r,h); gam=float(gammaincc(r,h+r))
  assert upper<=ext+2e-12 and lower<=ext+2e-12 and ext<=gam+2e-12
  print('alpha1 check',w,'h/H',factor,'upper',upper,'lower',lower,'ext',ext,'Gamma',gam)
print('Fifteen chosen actual-tail checks: PASS (floating-point diagnostics only)')
