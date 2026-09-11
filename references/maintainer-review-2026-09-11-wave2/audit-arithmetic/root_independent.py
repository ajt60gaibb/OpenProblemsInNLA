from pathlib import Path
import itertools,json
import sympy as s
out={};charts=0;forms=0
for n in range(1,5):
 for perm in itertools.permutations(range(n)):
  for signs in itertools.product([-1,1],repeat=n):
   roots=[None]*n
   for i in range(n):roots[perm[i]]=[signs[i] if j<=i else 0 for j in range(n)]
   for a in roots:
    assert all(v>=0 for v in a) or all(v<=0 for v in a);forms+=1
   for a in roots:
    for b in roots:
     for sign in [-1,1]:
      v=[a[j]+sign*b[j] for j in range(n)]
      assert all(x>=0 for x in v) or all(x<=0 for x in v);forms+=1
   charts+=1
out['primitive_forms']={'charts':charts,'forms':forms,'result':'PASS'}
a,b,c=s.symbols('a b c');x,y,z=s.symbols('x y z');raw=[x,y,z];gaps=[a,b,c]
poly=x**4*y**2+x**2*y**4+z**6-3*x*x*y*y*z*z
ref=s.expand(poly.subs({x:a,z:a+b,y:a+b+c},simultaneous=True))
sos=8*a**4*(b-c)**2+12*a**3*b*(b-c)**2+4*a*a*b*b*(b-c)**2+12*a**3*b**3+8*a**3*c**3+22*a*a*b**4+2*a*a*b*b*c*c+8*a*a*b*c**3+2*a*a*c**4+12*a*b**5+2*b**6
negative=0
for perm in itertools.permutations(range(3)):
 for signs in itertools.product([-1,1],repeat=3):
  sub={raw[perm[i]]:signs[i]*sum(gaps[:i+1]) for i in range(3)}
  q=s.Poly(poly.subs(sub,simultaneous=True),a,b,c)
  if any(v<0 for v in q.coeffs()):
   negative+=1;assert s.expand(q.as_expr()-ref)==0
   maj=sum(abs(co)*a**ex[0]*b**ex[1]*c**ex[2] for ex,co in q.terms())
   assert s.expand(3*q.as_expr()-maj-sos)==0
  else:assert all(v>=0 for v in q.coeffs())
assert negative==16
out['Motzkin']={'charts':48,'nontrivial_SOS_charts':negative,'result':'PASS'}
poly=(x*x-y)**2+x*x*y*y;q=s.Poly(poly.subs({y:a,x:a+b},simultaneous=True),a,b)
maj=sum(abs(co)*a**ex[0]*b**ex[1] for ex,co in q.terms());t=s.symbols('t')
assert s.expand(q.as_expr().subs({a:t*t,b:t-t*t},simultaneous=True)-t**6)==0
assert s.expand(maj.subs({a:t*t,b:t-t*t},simultaneous=True)-t**6-4*t**4)==0
out['isolated_zero_obstruction']='PASS'
# Universal-divisor arithmetic including all binary breakpoints.
for n in range(1,1001):
 g=n-((n+1).bit_length()-1)
 for k in range(n+1):assert n-(n-k).bit_count()>=g
out['universal_divisor_valuation']={'orders':1000,'result':'PASS'}
M=(2**128)*(2**61-1)
for n in range(2,36):
 q=2**(n-((n+1).bit_length()-1));assert 2*M>s.factorial(n)+q
assert s.factorial(34)/2<2**127
out['CRT_and_centered_reconstruction_bounds']='PASS'
p=Path(__file__).with_suffix('.json');p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
