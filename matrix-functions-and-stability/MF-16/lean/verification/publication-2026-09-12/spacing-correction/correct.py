from pathlib import Path
import json,hashlib,subprocess,os
R=Path('/tmp/nla-lean-mf16-worktree');E=R/'matrix-functions-and-stability/MF-16';P=E/'lean/verification/publication-2026-09-12';D=P/'spacing-correction';assert not D.exists();D.mkdir()
f=E/'README.md';data=f.read_bytes();(D/'README.initial.md').write_bytes(data)
r=subprocess.run(['git','diff','--check','HEAD'],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(D/'initial-diff-check.log').write_bytes(r.stdout);assert r.returncode==2 and r.stdout.count(b'trailing whitespace')==2
assert b'**Last checked:** 2026-09-12  \n**Status:** Lean verified  \n' in data
f.write_bytes(data.replace(b'**Last checked:** 2026-09-12  \n**Status:** Lean verified  \n',b'**Last checked:** 2026-09-12\n\n**Status:** Lean verified\n',1))
(D/'correction.json').write_text(json.dumps({'cause':'Inherited two-space Markdown endings on changed date/status metadata flagged by git diff --check. Use paragraph separation; original target unchanged.','first_pdf_marker':'Missed immediately before initial render; marker succeeded once before this corrective source edit. No claim of earlier execution.','pdf_marker_exit':0,'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest()},indent=2)+'\n')
env=os.environ.copy();env['PANDOC']='/tmp/nla-submission-tools/pandoc-3.11-arm64/bin/pandoc';env['XELATEX']='/Library/TeX/texbin/xelatex'
checks=[]
for n,args in [('format',['python3','tools/format_math.py','--check']),('render',['python3','tools/render_problems.py','MF-16']),('diff',['git','diff','--check','HEAD'])]:
 r=subprocess.run(args,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(D/(n+'.log')).write_bytes(r.stdout);checks.append(dict(name=n,command=args,exit_code=r.returncode));assert r.returncode==0,(n,r.stdout)
(D/'checks.json').write_text(json.dumps(checks,indent=2)+'\n');(D/'correct.py').write_bytes(Path(__file__).read_bytes())
V=Path('/tmp/nla-lean-formalization/mf16-publication-pages');before={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in V.glob('*.png')}
subprocess.run(['/opt/homebrew/bin/pdftoppm','-scale-to','1400','-png',str(E/'problem.pdf'),str(V/'page')],check=True)
after={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in V.glob('*.png')};print(json.dumps({'pixels_unchanged':before==after,'pdf_sha256':hashlib.sha256((E/'problem.pdf').read_bytes()).hexdigest(),'tex_sha256':hashlib.sha256((E/'problem.tex').read_bytes()).hexdigest()},indent=2))
(D/'pixel-check.json').write_text(json.dumps(dict(before=before,after=after,pixels_identical=before==after),indent=2)+'\n')
