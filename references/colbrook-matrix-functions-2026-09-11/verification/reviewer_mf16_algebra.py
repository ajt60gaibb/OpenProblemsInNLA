"""Independent exact algebra audit; optional dependency: SymPy 1.14.

Does not import submission code. Run from any directory; writes JSON to stdout.
The reviewed output is stored alongside this file as reviewer_mf16_algebra.json.
"""
import json
import sympy as s

a,b,c,t,p,g,r=s.symbols('a b c t p g r')
B=s.Matrix([[a,b],[b,c]])
X=s.diag(t,1)
Xr=s.diag(p,1)
basis=[s.Matrix([[1,0],[0,0]]),s.Matrix([[0,1],[1,0]]),s.Matrix([[0,0],[0,1]])]
dpowers=[s.diag(r*p/t,0),s.Matrix([[0,g],[g,0]]),s.diag(0,r)]
columns=[]
for E,D in zip(basis,dpowers):
    derivative=E*B*Xr*B*X+X*B*Xr*B*E+X*B*D*B*X
    columns.append(s.Matrix([derivative[0,0],derivative[0,1],derivative[1,1]]))
J=s.Matrix.hstack(*columns)
claimed=s.Matrix([
 [(r+2)*a*a*p*t+2*b*b*t,2*b*t*(a*g*t+a*p+c),r*b*b*t*t],
 [(r+1)*a*b*p+b*c,a*a*p*t+c*c+a*c*g*t+b*b*(g*t+p+t),b*t*(a*p+(r+1)*c)],
 [r*b*b*p/t,2*b*(a*p+c*(g+1)),(r+2)*c*c+2*b*b*p]])
assert all(s.expand(v)==0 for v in J-claimed)
detJ=s.expand(J[0,0]*(J[1,1]*J[2,2]-J[1,2]*J[2,1])
              -J[0,1]*(J[1,0]*J[2,2]-J[1,2]*J[2,0])
              +J[0,2]*(J[1,0]*J[2,1]-J[1,1]*J[2,0]))
H=(r+2)*(a*a*p*t+c*c+a*c*g*t)-(r-2)*b*b*(g*t+p+t)
claimed_det=p*t*(r+2)*(a*c-b*b)**2*H
residual=s.expand(t*(detJ-claimed_det))
assert s.expand(residual.subs(p,1+g*(t-1)))==0
specific={a:1,b:4,c:17,t:3,p:3**12,g:(3**12-1)//2,r:12}
J0=J.subs(specific)
P0=(X*B*Xr*B*X).subs(specific)
report={
 'derivative_matrix_symbolically_verified':True,
 'factorization_remainder_modulo_p_minus_1_minus_g_times_t_minus_1':0,
 'jacobian_at_counterexample':[[int(v) for v in J0.row(i)] for i in range(3)],
 'jacobian_determinant':int(J0.det()),
 'H12':int(H.subs(specific)),
 'P':[[int(v) for v in P0.row(i)] for i in range(2)],
 'detP':int(P0.det()),
 'passed':True}
assert report['jacobian_determinant']==-11785057051824
assert report['H12']==-527992
assert report['detP']==3**14
print(json.dumps(report,indent=2))
