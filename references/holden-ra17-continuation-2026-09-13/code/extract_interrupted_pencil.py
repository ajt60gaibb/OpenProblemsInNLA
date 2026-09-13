"""Extract, but do not validate, a homogeneous pencil from preserved research."""
from pathlib import Path
import ast,json
import sympy as s
ROOT=Path(__file__).resolve().parents[1]
P=ROOT/'exploratory/sparse_kernel5.py'
O=ROOT/'data/interrupted_pencil.json'
g={'__name__':'ra17_extraction','__file__':str(P)}
source=P.read_text(); tree=ast.parse(source)
for node in tree.body:
    if isinstance(node,ast.Expr):
        continue
    exec(compile(ast.Module(body=[node],type_ignores=[]),str(P),'exec'),g)
    for name,A in list(g.items()):
        if not isinstance(A,s.MatrixBase) or A.shape!=(4,4): continue
        xs=sorted(A.free_symbols,key=str)
        if len(xs)!=5: continue
        try:
            ps=[s.Poly(v,*xs) for v in A]
            if not all(p.total_degree()<=1 and p.eval(dict.fromkeys(xs,0))==0 for p in ps): continue
            bases=[A.diff(x) for x in xs]
            if not all(c.is_Rational for B in bases for c in B): continue
            if s.Matrix.hstack(*[s.Matrix(list(B)) for B in bases]).rank()!=5:continue
        except (s.PolynomialError,TypeError):continue
        O.write_text(json.dumps({'source':str(P),'variable':name,'parameters':[str(x) for x in xs],
          'basis':[[[str(B[i,j]) for j in range(4)] for i in range(4)] for B in bases]},indent=2))
        print('EXTRACTED',name, str(A)); raise SystemExit(0)
raise SystemExit('No five-parameter homogeneous rational pencil extracted')
