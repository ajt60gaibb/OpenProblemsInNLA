#!/usr/bin/env python3
"""Finite exact diagnostics and source binding; not a Lean proof certificate."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from math import comb
import hashlib
import json
import re
import shutil
import subprocess

HERE=Path(__file__).resolve().parent
BASE=Path('/tmp/nla-lean-next-20260915')
P=BASE/'matrix-functions/MF-12'
REPO=Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
UPSTREAM='8f04b905eb2e0827b6b84f37d9d080ae1f05b202'
DEVELOPMENT='a1efcbfc59263b9e5bb00914ee709112348c1e54'
MATHLIB=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages/mathlib')

def sha(b): return hashlib.sha256(b).hexdigest()
def read(p): return json.loads(p.read_text())
def git(commit,f):return subprocess.check_output(['git','show',f'{commit}:{f}'],cwd=REPO)
def save(p,d):p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def keep(src,rel):
    dest=HERE/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
    return sha(dest.read_bytes())

source_files={}
for f in sorted(P.glob('*')):
    if f.is_file():source_files[f.name]=keep(f,Path('source')/f.name)
for f in sorted((P/'NLA').rglob('*.lean')):
    rel=f.relative_to(P);source_files[str(rel)]=keep(f,Path('source')/rel)
canonical={}
prov=read(P/'SOURCE-PROVENANCE.json')
for obj in prov['sources']:
    b=git(UPSTREAM,obj['canonical_path'])
    assert sha(b)==obj['sha256'] and b==(P/obj['retained_path']).read_bytes()
    dest=HERE/'canonical'/obj['canonical_path'];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
    canonical[obj['canonical_path']]=sha(b)

freeze=read(P/'STATEMENT-FREEZE.json')
assert freeze['statement_count']==28
for f,h in freeze['frozen_files_sha256'].items():assert source_files[f]==h,f
frozen_reviews={}
for obj in freeze['reviews']:
    f=P/obj['retained_path'];assert sha(f.read_bytes())==obj['sha256']
    frozen_reviews[obj['retained_path']]=keep(f,Path('source')/obj['retained_path'])

config=read(P/'comparator.json')
assert config['definition_names']==[] and len(config['theorem_names'])==28
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
alllean={f:(P/f).read_text() for f in source_files if f.endswith('.lean')}
proof={f:s for f,s in alllean.items() if f!='Challenge.lean'}
assert len(proof)==19
assert len(re.findall(r'\bby sorry\b',alllean['Challenge.lean']))==28
for f,s in proof.items():
    assert not re.search(r'\b(sorry|admit|native_decide|sorryAx|run_tac|unsafe)\b',
                         re.sub(r'/\-[\s\S]*?\-/', '',s)),f
    assert not re.search(r'^\s*(axiom|opaque|#eval)\b',s,re.M),f
    assert 'import Challenge' not in s

def statement(text,name):
    m=re.search(r'^theorem '+re.escape(name)+r'\b([\s\S]*?)\s*:=',text,re.M)
    assert m,name
    return re.sub(r'\s+',' ',m.group(1)).strip()

contracts={}
for qualified in config['theorem_names']:
    name=qualified.removeprefix('NLA.MF12.')
    expected=statement(alllean['Challenge.lean'],name)
    hits=[(f,statement(s,name)) for f,s in proof.items() if re.search(r'^theorem '+name+r'\b',s,re.M)]
    assert len(hits)==1 and hits[0][1]==expected,(name,hits)
    assert '#assert_trust kernel '+qualified in proof['Solution.lean']
    contracts[qualified]={'file':hits[0][0],'whitespace_normalized_statement_sha256':sha(expected.encode())}

edges={}
for f,s in proof.items():
    edges[f]=[]
    for mod in re.findall(r'^import\s+(NLA\.MF12\.\w+)\s*$',s,re.M):
        dep=mod.replace('.','/')+'.lean';assert dep in proof;edges[f].append(dep)
seen=set();active=set()
def walk(f):
    assert f not in active,('cycle',f)
    if f in seen:return
    active.add(f)
    for child in edges[f]:walk(child)
    active.remove(f);seen.add(f)
walk('Solution.lean')
assert seen==set(proof)

development_mapping={}
for f in alllean:
    remote='Challenges/MF12.lean' if f=='Challenge.lean' else 'NLA/MF12/Solution.lean' if f=='Solution.lean' else f
    b=git(DEVELOPMENT,'.lean-development/'+remote)
    assert sha(b)==source_files[f],f
    development_mapping[f]={'path':'.lean-development/'+remote,'sha256':sha(b)}

api={}
for f in ['Mathlib/Analysis/CStarAlgebra/Matrix.lean','Mathlib/Analysis/MeanInequalities.lean',
          'Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean','Mathlib/Analysis/SpecialFunctions/Pow/Real.lean',
          'Mathlib/LinearAlgebra/Matrix/Kronecker.lean','Mathlib/Data/Nat/Log.lean',
          'Mathlib/Data/Nat/Choose/Bounds.lean','Mathlib/Data/Set/Finite/List.lean']:
    api[f]=keep(MATHLIB/f,Path('api-source')/f)

# Independent exact matrix operations for the source pair at alpha=1/2.
def mat(rows):return tuple(tuple(map(Q,r)) for r in rows)
def ident(n):return tuple(tuple(Q(i==j) for j in range(n)) for i in range(n))
def mul(a,b):
    assert len(a[0])==len(b)
    return tuple(tuple(sum((a[i][k]*b[k][j] for k in range(len(b))),Q(0))
                       for j in range(len(b[0]))) for i in range(len(a)))
def power(a,n):
    z=ident(len(a))
    while n:
        if n%2:z=mul(z,a)
        n//=2
        if n:a=mul(a,a)
    return z
def chronological(ms,n):
    z=ident(n)
    for a in ms:z=mul(a,z)
    return z
def kron(a,b):
    return tuple(tuple(a[i][j]*b[r][s] for j in range(len(a[0])) for s in range(len(b[0])))
                 for i in range(len(a)) for r in range(len(b)))
lam=Q(1,4);mu=Q(1,2)
A=mat([[1,0,0,0,0,0],[0,lam,lam,0,0,0],[0,0,lam,0,0,0],
       [0,0,0,mu,mu,0],[0,0,0,0,mu,0],[0,0,0,0,0,1]])
U=mat([[1,-1,0,1,0,0],[0,0,0,0,0,1]])
V=mat([[1,0],[0,0],[1,0],[0,0],[0,1],[0,1]])
Pmat=mul(V,U)
assert mul(U,V)==ident(2) and mul(Pmat,Pmat)==Pmat and A!=Pmat
checks={'projection_identities':3}
def loss(q):return q*lam**q
def gain(q):return q*mu**q
def compressed(q):return mat([[1-loss(q),gain(q)],[0,1]])
for q in range(21):
    assert mul(mul(U,power(A,q)),V)==compressed(q)
    assert 0<=loss(q)<=Q(1,4)
    assert gain(q)**2==q*loss(q)
checks['compressed_power_and_loss_gain_cases']=21

gapcount=0
for size in range(5):
    for qs in product(range(5),repeat=size):
        weights=[]
        for i in range(size):
            w=Q(1)
            for q in qs[i+1:]:w*=1-loss(q)
            weights.append(w)
        a=Q(1)
        for q in qs:a*=1-loss(q)
        z=sum((gain(q)*w for q,w in zip(qs,weights)),Q(0))
        assert sum((loss(q)*w for q,w in zip(qs,weights)),Q(0))==1-a
        assert 0<=a<=1 and all(0<=w<=1 for w in weights)
        assert chronological([compressed(q) for q in qs],2)==mat([[a,z],[0,1]])
        assert 0<=z and z*z<=sum(qs)
        gapcount+=1
checks['arbitrary_gap_lists_empty_and_zero_included']=gapcount

wordcount=0
for length in range(8):
    for word in product([False,True],repeat=length):
        qs=[0]
        for bit in word:
            if bit:qs.append(0)
            else:qs[-1]+=1
        assert sum(qs)+len(qs)-1==length
        rebuilt=[]
        for j,q in enumerate(qs):
            if j:rebuilt.append(True)
            rebuilt.extend([False]*q)
        assert rebuilt==list(word)
        W=chronological([Pmat if b else A for b in word],6)
        if len(qs)==1:assert W==power(A,qs[0])
        else:
            B=chronological([compressed(q) for q in qs[1:-1]],2)
            actual=mul(mul(mul(mul(power(A,qs[-1]),V),B),U),power(A,qs[0]))
            assert W==actual
        wordcount+=1
checks['all_binary_words_through_length7']=wordcount

for n in range(4,10001):
    q=0
    while 4**(q+1)<=n:q+=1
    k=n//(q+1);r=n-k*(q+1)
    assert q>=1 and k>=1 and 4**q<=n<4**(q+1)
    assert 2*(q+1)<=4**q and r+k*(q+1)==n
    assert k*loss(q)>=Q(1,4)
checks['exact_log_division_mass_cases']=9997
for n in range(1,65):
    if n<4:
        assert power(A,n)[0][0]==1 and Q(n,400)<=1
    else:
        q=0
        while 4**(q+1)<=n:q+=1
        k=n//(q+1);r=n-k*(q+1)
        W=mul(power(A,r),power(mul(Pmat,power(A,q)),k))
        z=gain(q)/loss(q)*(1-(1-loss(q))**k)
        assert mul(W,V)[0][1]==z
        assert (1-loss(q))**k<=1/(1+k*loss(q))
        assert 1-(1-loss(q))**k>=Q(1,5)
        assert z>=0 and (10*z)**2>=n
checks['lower_word_actual_matrix_cases']=64

for m in range(7):
    J=tuple(tuple(Q(i==j)+Q(i+1==j) for j in range(m+1)) for i in range(m+1))
    for n in range(13):
        expected=tuple(tuple(Q(comb(n,j-i)) if i<=j and j-i<=n else Q(0)
                             for j in range(m+1)) for i in range(m+1))
        assert power(J,n)==expected
        if m<=n:assert n**m<=m**m*comb(n,m)
        else:assert n**m<=m**m
        if n>=1:assert all(abs(v)<=n**m for row in expected for v in row)
checks['Jordan_matrix_and_binomial_cases']=91

B=mat([[1,-2],[3,1]]);D=mat([[2,0],[-1,1]]);J=mat([[1,1],[0,1]])
tensorcount=0
for length in range(5):
    for word in product([False,True],repeat=length):
        lhs=chronological([kron(D,J) if b else kron(B,J) for b in word],4)
        rhs=kron(chronological([D if b else B for b in word],2),power(J,length))
        assert lhs==rhs
        tensorcount+=1
checks['noncommutative_tensor_word_cases']=tensorcount

save(HERE/'INPUTS.json',{'source_files':source_files,'canonical_files':canonical,
    'frozen_reviews':frozen_reviews,'api_source_sha256':api,'development_git_mapping':development_mapping,
    'canonical_source_commit':UPSTREAM,'development_source_commit':DEVELOPMENT,
    'scope':'Complete mathematical source review; not canonical runtime acceptance'})
save(HERE/'CHECKS.json',{'exact_diagnostic_cases':checks,'sum_of_case_counts':sum(checks.values()),
    'frozen_files_unchanged':len(freeze['frozen_files_sha256']),
    'all_28_normalized_contracts':contracts,'all_19_Lean_inputs_reachable_without_Challenge':True,
    'local_import_graph':edges,'no_holes_custom_axioms_native_or_unsafe_in_implementation':True,
    'full_19_Lean_inputs_and_Challenge_match_development_Git':True,
    'scope':'Exact finite diagnostics complement source reading; they are not a universal mathematical proof or kernel certificate',
    'no_local_Lean_Lake_cache':True})
print(json.dumps({'source_files':len(source_files),'frozen_files':len(freeze['frozen_files_sha256']),
 'proof_Lean_files':len(proof),'targets':len(contracts),'diagnostic_case_counts':checks,
 'INPUTS_sha256':sha((HERE/'INPUTS.json').read_bytes()),'CHECKS_sha256':sha((HERE/'CHECKS.json').read_bytes())},indent=2))
