"""Verify the KE-05 source binding, preservation, conversion, links and privacy."""
from pathlib import Path
from hashlib import sha256
import json, os, re, subprocess
r=Path(__file__).resolve().parent; w=r.parents[1]
p=w/'randomized-and-low-rank-approximation/KE-05'
pandoc=os.environ.get('PANDOC','pandoc')
def digest(x): return sha256(x.read_bytes()).hexdigest()
def math_nodes(path, fmt):
    ast=json.loads(subprocess.check_output([pandoc,'-f',fmt,'-t','json',str(path)],text=True))
    nodes=[]
    def walk(x):
        if isinstance(x,dict):
            if x.get('t')=='Math': nodes.append(re.sub(r'\s+','',x['c'][1]))
            else:
                for v in x.values(): walk(v)
        elif isinstance(x,list):
            for v in x: walk(v)
    walk(ast['blocks']); return nodes
assert digest(r/'reviewed-proof.md')=='51e66685d6e84639ee3aa098ebf1e91e43891c9a6fe04d473f334cf0e6f2a68f'
assert digest(r/'independent-review.md')=='3ab2ca8173e80b8f2c2506ebd7b2d54387ca2d8a65fdcae6ac29042a31bdc360'
assert digest(p/'solution.md')=='31c3416ba212cb2cbb73d126633efe79f1e4a2669a80ef5936fa12dc6723bd62'
a=(r/'reviewed-proof.md').read_text(); b=(p/'solution.md').read_text()
def core(s): return s[s.index('## Exact target and conclusion'):s.index('## Scope, attribution, and verification limits')]
assert core(a)==core(b)
base=(r/'canonical-statement.md').read_text(); canonical=(p/'README.md').read_text()
original=base[base.index('Fix integers'):base.index('<!-- navigation -->')]
assert canonical.count(original)==1
assert '**Status:** Solved' in canonical
assert json.loads((w/'problem_ids.json').read_text())['KE-05']=='randomized-and-low-rank-approximation/KE-05/README.md'
formula_counts={}
for stem in ['solution','problem']:
    md=p/('solution.md' if stem=='solution' else 'README.md')
    m=math_nodes(md,'markdown+tex_math_dollars+raw_tex')
    t=math_nodes(p/(stem+'.tex'),'latex')
    assert m==t, (stem,len(m),len(t),next(((i,x,y) for i,(x,y) in enumerate(zip(m,t)) if x!=y),None))
    formula_counts[stem]=len(m)
public_md=[p/'solution.md',p/'README.md',r/'README.md',r/'independent-review.md',r/'source-notes.md',r/'public-audit/README.md',r/'public-audit/KE-05-source-scope-review.md']
for f in public_md:
    for target in re.findall(r'\]\(([^)]+)\)',f.read_text()):
        if '://' in target or target.startswith('#'): continue
        dest=(f.parent/target.split('#',1)[0]).resolve()
        assert dest.exists(),(str(f),target)
email=re.compile(r'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}')
texts=[]
for f in list(r.rglob('*'))+list(p.iterdir()):
    if not f.is_file() or f.suffix not in ['.md','.tex','.json','.py','.txt']: continue
    assert not email.search(f.read_text()),f
    texts.append(str(f.relative_to(w)))
for stem in ['solution','problem']:
    text=subprocess.check_output(['pdftotext',str(p/(stem+'.pdf')),'-'],text=True)
    assert not email.search(text)
    for required in ['George Stepaniants','Department of Computing and Mathematical Sciences','California Institute of Technology']:
        assert required in ' '.join(text.split()),(stem,required)
for required in ['George Stepaniants','Department of Computing and Mathematical Sciences','California Institute of Technology']:
    for text in [b,canonical,(w/'RESOLVED.md').read_text()]: assert required in text
report={'status':'PASS','reviewed_source_binding':'PASS','public_source_binding':'PASS','full_mathematical_core_identical':True,'original_target_and_history_retained':True,'formulas_identical_in_order':formula_counts,'relative_links':'PASS','author_affiliation':'PASS','no_contact_email':'PASS','text_files_checked':len(texts),'artifacts':{str(f.relative_to(w)):{'bytes':f.stat().st_size,'sha256':digest(f)} for f in sorted(p.iterdir()) if f.is_file()}}
print(json.dumps(report,indent=2))
