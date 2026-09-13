import json
from pathlib import Path
from itertools import combinations
import numpy as np

root=Path('/private/tmp/nla-audit-186/references/holden-matrix-2026-09-12/MI-15')
rng=np.random.default_rng(1860912)
results=[]
for n in range(8,13):
    data=json.loads((root/f'certificates/n{n}.json').read_text())
    D=data['gram_denominator']; labels=[a for a in range(1-n,n) if a]
    pairs=list(combinations(labels,2)); index={p:i for i,p in enumerate(pairs)}
    basis={a:np.array([[int(i-j==a) for j in range(n)] for i in range(n)],dtype=object) for a in labels}
    C=np.column_stack([(basis[a]@basis[b]-basis[b]@basis[a]).reshape(-1) for a,b in pairs])
    Q=D*(2*np.diag(np.array([(n-abs(a))*(n-abs(b)) for a,b in pairs],dtype=object))-C.T@C)
    for a,b,c,d,t in data['plucker_coefficients']:
        for p,q,s in [((a,b),(c,d),1),((a,c),(b,d),-1),((a,d),(b,c),1)]:
            i,j=index[p],index[q];Q[i,j]+=s*t;Q[j,i]+=s*t
    groups=[[i for i,(a,b) in enumerate(pairs) if b-a==2*(n-1)-k] for k in range(n-1)]
    eye=np.eye(len(pairs),dtype=object);cols=[];covered=set()
    for group in groups:
        assert group and not(covered & set(group));covered.update(group)
        assert all(v == 0 for v in Q@sum((eye[:,i] for i in group)))
        cols += [eye[:,i]-eye[:,group[0]] for i in group[1:]]
    cols += [eye[:,i] for i in range(len(pairs)) if i not in covered]
    B=np.column_stack(cols);G=B.T@Q@B;T=np.array(data['congruence_numerators'],dtype=object)
    H=T.T@G@T
    assert np.array_equal(H,H.T)
    margins=[H[i,i]-sum(abs(H[i,j]) for j in range(len(H)) if j!=i) for i in range(len(H))]
    assert min(margins)>0 and min(margins)==int(data['integer_diagonal_dominance_minimum'])
    for _ in range(25):
        x={a:int(v) for a,v in zip(range(1-n,n),rng.integers(-6,7,2*n-1))}
        y={a:int(v) for a,v in zip(range(1-n,n),rng.integers(-6,7,2*n-1))}
        X=np.array([[x[i-j] for j in range(n)] for i in range(n)],dtype=object)
        Y=np.array([[y[i-j] for j in range(n)] for i in range(n)],dtype=object)
        comm=X@Y-Y@X
        target=2*sum((X*X).flat)*sum((Y*Y).flat)-2*sum((X*Y).flat)**2-sum((comm*comm).flat)
        z=np.array([x[a]*y[b]-x[b]*y[a] for a,b in pairs],dtype=object)
        represented=z@Q@z+2*n*D*sum((n-abs(a))*(x[0]*y[a]-x[a]*y[0])**2 for a in labels)
        assert D*target==represented
    results.append({'n':n,'rank':len(H),'minimum_integer_margin':str(min(margins)),'exact_toeplitz_evaluations':25,'result':'PASS'})
print(json.dumps(results,indent=2))
Path('/private/tmp/nla-pr186-independent-mi15.json').write_text(json.dumps(results,indent=2)+'\n')
