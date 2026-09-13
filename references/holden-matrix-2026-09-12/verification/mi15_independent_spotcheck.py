import importlib.util,random,json
from pathlib import Path
p=Path(__file__).resolve().parents[1] / 'MI-15'
s=importlib.util.spec_from_file_location('v',p/'verify_exact.py'); v=importlib.util.module_from_spec(s);s.loader.exec_module(v)
r=random.Random(1592026)
for n in range(8,13):
 data=json.loads((p/f'certificates/n{n}.json').read_text()); pairs,Q=v.gram_from_certificate(data); D=data['gram_denominator']
 poly=v.canonical_polynomial(n)
 for case in range(25):
  x={a:r.randrange(-3,4) for a in range(1-n,n)};y={a:r.randrange(-3,4) for a in range(1-n,n)}
  X=[[x[i-j] for j in range(n)] for i in range(n)];Y=[[y[i-j] for j in range(n)] for i in range(n)]
  xx=sum(t*t for row in X for t in row);yy=sum(t*t for row in Y for t in row);xy=sum(X[i][j]*Y[i][j] for i in range(n) for j in range(n))
  cc=sum(sum(X[i][k]*Y[k][j]-Y[i][k]*X[k][j] for k in range(n))**2 for i in range(n) for j in range(n))
  target=2*xx*yy-2*xy*xy-cc
  assert target==sum(c*x[a]*x[b]*y[e]*y[f] for (a,b,e,f),c in poly.items())
  z=[x[a]*y[b]-x[b]*y[a] for a,b in pairs]
  represented=sum(z[i]*Q[i][j]*z[j] for i in range(len(z)) for j in range(len(z)))+D*sum(2*n*(n-abs(a))*(x[0]*y[a]-x[a]*y[0])**2 for a in x if a)
  assert represented==D*target
 # Force a polynomial-identity failure independently of PSD tests.
 Q[0][0]+=1
 try:v.check_polynomial(n,D,pairs,Q)
 except AssertionError:pass
 else:raise AssertionError('diagonal mutation accepted')
 print(f'n={n}: 25 direct integer matrix/quartic/Gram comparisons PASS; diagonal corruption rejected')
