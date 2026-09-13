from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, subprocess, shutil

R = Path('/tmp/nla-lean-ra08-worktree')
E = R/'randomized-and-low-rank-approximation/RA-08'
P = E/'lean'
D = P/'verification/canonical-reproduction-addendum-2026-09-13'
h = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
old = json.loads((D/'ADDENDUM.json').read_text())
diag = D/'initial-layout-diagnostic'
diag.mkdir()
for f in ['README.md', 'problem.tex', 'problem.pdf']:
    shutil.copyfile(E/f, diag/f)
for f in ['ADDENDUM.json', 'pdf-text.txt']:
    shutil.copyfile(D/f, diag/f)
(diag/'root-finding.json').write_text(json.dumps({
    'finding': 'Root displayed all four PNGs. The original implication was split across pages 2 and 3, leaving most of page 3 empty before the renderer-required reference page.',
    'correction': 'Pair exact declaration names in seven list items, retaining all fourteen names and unchanged mathematical text, to keep the original implication together.',
    'original_images': old['pdf_images']
}, indent=2)+'\n')
t = (E/'README.md').read_text()
names = [x.removeprefix('NLA.RA08.') for x in old['checked_names']]
before = ''.join('- `'+x+'`\n' for x in names)
after = ''.join('- `'+names[i]+'`, `'+names[i+1]+'`\n' for i in range(0,14,2))
assert t.count(before) == 1
t = t.replace(before,after)
marker = 'Let $`n\\ge2`$'
assert hashlib.sha256(t[t.index(marker):].encode()).hexdigest() == old['original_target_suffix_sha256']
(E/'README.md').write_text(t)
env = os.environ.copy()
env['PANDOC'] = '/tmp/nla-submission-tools/pandoc-3.11-arm64/bin/pandoc'
env['XELATEX'] = '/Library/TeX/texbin/xelatex'
A = D/'layout-checks'; A.mkdir()
checks=[]
for label, args in [('format',['python3','tools/format_math.py','--check']),('render',['python3','tools/render_problems.py','RA-08']),('diff-check',['git','diff','--check','HEAD'])]:
    r=subprocess.run(args,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=A/(label+'.log');log.write_bytes(r.stdout)
    checks.append(dict(command=args,exit_code=r.returncode,log=str(log.relative_to(D)),log_sha256=h(log)))
    assert r.returncode==0,(label,r.stdout.decode())
V=Path('/tmp/nla-lean-formalization/ra08-reproduction-addendum-final-pages');V.mkdir()
subprocess.run(['/opt/homebrew/bin/pdftoppm','-scale-to','1400','-png',str(E/'problem.pdf'),str(V/'page')],check=True)
(D/'pdf-text.txt').write_bytes(subprocess.check_output(['/opt/homebrew/bin/pdftotext','-layout',str(E/'problem.pdf'),'-']))
for r,v in old['all_existing_project_files_preserved'].items(): assert h(P/r)==v,r
old['utc']=datetime.now(timezone.utc).isoformat()
old['current_publication_files']={r:h(R/r) for r in old['current_publication_files']}
old['after_canonical_files']={r:h(R/r) for r in old['after_canonical_files']}
old['checks']+=checks
old['pdf_images']={str(f):h(f) for f in sorted(V.glob('*.png'))}
old['layout_correction']='Initial complete four-page rendering and root finding retained in initial-layout-diagnostic; paired exact declarations keep the original mathematical statement together.'
(D/'ADDENDUM.json').write_text(json.dumps(old,indent=2)+'\n')
(D/'refine_layout.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'pages':list(old['pdf_images']),'pdf':h(E/'problem.pdf'),'tex':h(E/'problem.tex')},indent=2))
