"""Independent exact reconstruction, with receipt/source identity checks."""
from pathlib import Path
import hashlib, json, re, subprocess
import sympy as s

root = Path(__file__).resolve().parents[1]
R = s.Rational
A = s.Matrix([[1,R(3,4),0],[0,0,0],[0,0,0]])
B = s.Matrix([[-1,0,0],[0,0,0],[-R(3,4),0,0]])
RA = s.Matrix([[R(4,5),R(3,5),0],[R(3,5),R(9,20),0],[0,0,0]])
E = s.diag(R(5,4),0,0)
LB = s.Matrix([[R(4,5),0,R(3,5)],[0,0,0],[R(3,5),0,R(9,20)]])
RS, LS = s.diag(R(3,4),R(3,4),0),s.diag(R(3,4),0,R(3,4))
for X,Y in [(A,RA),(A.T,E),(B,E),(B.T,LB),(A+B,RS),((A+B).T,LS)]:
    assert Y*Y == X.T*X and all(e>=0 for e in Y.eigenvals())
SA,SB,SS = (RA+E)/2,(E+LB)/2,(RS+LS)/2
u,v=s.Matrix([3,1,0]),s.Matrix([3,0,1])
assert SA==s.eye(3)/8+u*u.T/10-s.diag(0,0,1)/8
assert SB==s.eye(3)/8+v*v.T/10-s.diag(0,1,0)/8
assert SS==s.diag(R(3,4),R(3,8),R(3,8))
assert s.sqrt(2)/4<R(3,8)
P=s.diag(1,0); Q=s.Matrix([[144,60],[60,25]])/169
X=s.Matrix([[0,R(5,12)],[0,0]])
assert P*P==P and Q*Q==Q and (P+Q).det()==R(25,169)
for Z,Y in [(P,P),(P.T,P),(X,R(5,12)*(s.eye(2)-P)),(X.T,R(5,12)*P),(P+X,R(13,12)*Q),((P+X).T,R(13,12)*P)]:
    assert Y*Y==Z.T*Z and all(e>=0 for e in Y.eigenvals())
assert R(13,6)-R(11,6)==R(1,3)

summary={'exact_MI06_six_moduli_and_decompositions':'PASS','exact_MI07_six_moduli_projectors_trace':'PASS','receipts':{}}
allowed={'propext','Classical.choice','Quot.sound'}
for name,pr in [('mi06',167),('mi07',166)]:
    receipt=next((root/'reports'/f'{name}-ci').rglob('result.json'))
    d=json.loads(receipt.read_text()); project=root/f'pr{pr}'/d['project']
    assert d['result']=='comparator-accepted'
    assert all(hashlib.sha256((project/f).read_bytes()).hexdigest()==h for f,h in d['input_sha256'].items())
    files=subprocess.check_output(['git','ls-files','--',d['project']],cwd=root/f'pr{pr}',text=True).splitlines()
    assert {str(Path(f).relative_to(d['project'])) for f in files}==set(d['input_sha256'])
    assert d['config']==json.loads((project/'comparator.json').read_text())
    assert hashlib.sha256((root/f'pr{pr}'/'tools/lean/source-lock.json').read_bytes()).hexdigest()==d['source_lock_sha256']
    log=(receipt.parent/'comparator.log').read_text()
    ax=re.findall(r'depends on axioms: \[([^]]*)\]',log,re.S)
    assert ax and all(set(x.strip() for x in a.split(','))<=allowed for a in ax)
    assert 'Lean default kernel accepts the solution' in log and 'Your solution is okay!' in log
    for control in ['sandbox','kernel-controls','comparator-controls']:
        assert (receipt.parent/f'{control}.log').read_text().rstrip().endswith('EXIT_STATUS=0')
    for control,axiom in [('negative-sorry','sorryAx'),('negative-native','checked._native.native_decide.ax_1_1')]:
        t=(receipt.parent/f'{control}.log').read_text()
        assert f"Illegal axiom detected: '{axiom}'" in t and t.rstrip().endswith('EXIT_STATUS=1')
    summary['receipts'][name]={'commit':d['repository_commit'],'inputs':len(files),'axiom_reports':len(ax),'declarations':d['config']['theorem_names'],'result':d['result'],'zip_sha256':hashlib.sha256((root/'reports'/f'{name}-ci.zip').read_bytes()).hexdigest()}
out=root/'reports'/'mi06-mi07-independent.json'
out.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
