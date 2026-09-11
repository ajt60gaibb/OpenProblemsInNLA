from pathlib import Path
import hashlib, importlib.util, json
import sympy as s

base=Path(__file__).resolve().parent
source=base.parent/'submission'
out=base/'fresh-results'
spec=importlib.util.spec_from_file_location('critical',base/'TR-17/verify_critical_examples.py')
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
x,y=s.symbols('x y')
tests=[]
def record(name,condition,detail=None):
    assert condition,name
    tests.append({'name':name,'pass':True,'detail':detail})
record('standard monomials: length of (x^2,y^3)',mod.quotient_length([x*x,y**3],(x,y))==6)
record('standard monomials: nonreduced length of (x^3,y-x)',mod.quotient_length([x**3,y-x],(x,y))==3)
record('unit ideal length zero',mod.quotient_length([1],(x,y))==0)
try:
    mod.quotient_length([x],(x,y))
    raise AssertionError('positive-dimensional ideal not rejected')
except mod.VerificationFailure:
    record('positive-dimensional ideal rejected',True)
z=s.symbols('z0:3')
A=z[0]**2+z[1]**2+z[2]**2
B=z[0]**2+z[1]**2+2*z[2]**2
q=s.Poly(A*B**2,*z)
exponents=[(a,b,3-a-b) for a in range(4) for b in range(4-a)]
mon=s.Matrix([s.prod(t**e for t,e in zip(z,E)) for E in exponents])
gram=s.diag(*[q.coeff_monomial(s.prod(t**(2*e) for t,e in zip(z,E))) for E in exponents])
record('ternary-cubic Gram pullback equals A B^2',s.expand((mon.T*gram*mon)[0]-q.as_expr())==0)
record('two conics have no common component',s.gcd(A,B)==1)
record('reduced conic support squarefree',s.Poly(A*B,*z).sqf_part().monic()==s.Poly(A*B,*z).monic())
node=1+(x-y)**2+4*x*x*y*y
record('nodal biquadric squarefree on main chart',s.Poly(node,x,y).sqf_part().monic()==s.Poly(node,x,y).monic())
coords=(out/'TR-27-coordinates.json').read_text(encoding='utf-8')
old=(source/'TR-27/coordinates.json').read_text(encoding='utf-8')
record('TR27 fresh coordinates JSON equals supplied evidence',json.loads(coords)==json.loads(old))
record('TR27 coordinates differ only by CRLF conversion',coords==old)
comparisons=[]
for a,b in [('TR-17/verification.txt','TR-17-verify.log'),('TR-17/critical_verification.txt','TR-17-verify_critical_examples.log'),('TR-27/verification.txt','TR-27-verify.log')]:
    oldlines=(source/a).read_text(encoding='utf-8').splitlines()
    newlines=(out/b).read_text(encoding='utf-8').splitlines()
    differences=[{'old':v,'new':w} for v,w in zip(oldlines,newlines) if v!=w]
    comparisons.append({'supplied':a,'fresh':b,'old_lines':len(oldlines),'new_lines':len(newlines),'differences':differences})
report={'sympy':s.__version__,'checks':tests,'transcript_comparisons':comparisons}
(out/'reviewer-checks.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
manifest_path=out/'manifest.json'
manifest=json.loads(manifest_path.read_text(encoding='utf-8'))
manifest['tr27_coordinates_normalized_text_identical']=True
manifest['tr27_coordinates_json_equal']=True
manifest['output_files']=[{'path':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in sorted(out.iterdir()) if p.is_file() and p.name!='manifest.json']
manifest['reviewer_script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
manifest_path.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
