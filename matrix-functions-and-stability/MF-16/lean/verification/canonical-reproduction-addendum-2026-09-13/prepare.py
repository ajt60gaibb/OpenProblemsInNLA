from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,re,os,shutil
CASES=[('MF-16','mf16','matrix-functions-and-stability','4e24448897a088ca9e7458379add1014c5d11e0c','NLA.MF16.not_wordUniquenessConjecture','## Problem statement'),('RA-08','ra08','randomized-and-low-rank-approximation','de6513d726e3f66d20730fdaef5ba99318ee7e8b','NLA.RA08.not_concaveSpectralTransferConjecture','Let $`n\\ge2`$')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();env=os.environ.copy();env['PANDOC']='/tmp/nla-submission-tools/pandoc-3.11-arm64/bin/pandoc';env['XELATEX']='/Library/TeX/texbin/xelatex'
for ID,tree,cat,C,main,marker in CASES:
 R=Path('/tmp/nla-lean-'+tree+'-worktree');E=R/cat/ID;P=E/'lean';D=P/'verification/canonical-reproduction-addendum-2026-09-13'
 if D.exists():
  assert ID=='MF-16' and not (D/'ADDENDUM.json').exists();diag=D/'initial-render-diagnostic';diag.mkdir()
  for n in ['README.md','problem.tex']:(diag/n).write_bytes((E/n).read_bytes())
  (diag/'initial_authoring.py.txt').write_bytes(Path('/tmp/nla-lean-formalization/add_canonical_reproduction_mf16_ra08.py').read_bytes())
  (diag/'correction.json').write_text(json.dumps({'failure':'Initial XeLaTeX render failed because bash syntax highlighting requests an undefined Shaded environment; long inline hash/name paragraphs also overflowed. Full initial render.log retained at parent.','fix':'Use supported plain code fences, one declaration per list item, separate dependency-pin list items and split shell command arguments. No shared renderer/template or mathematics change.','exit_code':1},indent=2)+'\n')
 else:
  D.mkdir();(D/'archive').mkdir()
  for n in ['README.md','problem.tex','problem.pdf']:(D/'archive'/n).write_bytes((E/n).read_bytes())
 diag=Path('/tmp/nla-lean-formalization/reproduction-addendum-diagnostic')
 for f in diag.iterdir():(D/('initial-syntax-'+f.name)).write_bytes(f.read_bytes())
 prior={str(f.relative_to(P)):sha(f) for f in P.rglob('*') if f.is_file() and not f.is_relative_to(D)}
 initial_pub=P/('verification/publication-2026-09-12' if ID=='MF-16' else 'verification/publication-2026-09-13');initial=json.loads((initial_pub/'INTEGRITY-CHECKS.json').read_text())['publication_files']
 before={str((E/n).relative_to(R)):sha(D/'archive'/n) for n in ['README.md','problem.tex','problem.pdf']}
 assert all(initial[r]==h for r,h in before.items())
 text=(D/'archive/README.md').read_text();suffix=text[text.index(marker):];config=json.loads((P/'comparator.json').read_text());names=config['theorem_names'];assert names[-1]==main and len(names)==(9 if ID=='MF-16' else 14);ns=main.rsplit('.',1)[0]
 block='### Checked declarations, versions and reproduction\n\nThe full original target is refuted by `'+main+'`. All checked declarations in namespace `'+ns+'` are listed below; their individual contracts and source correspondence are in the [proof package](lean/README.md).\n\n'
 block+=''.join('- `'+n.removeprefix(ns+'.')+'`\n' for n in names)+'\n'
 block+='The exact checked versions are:\n\n- Lean **4.33.1**.\n- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.\n- LeanCert: `621a43d7cf21f87872392a01e874f2f1dbddc926`.\n\nThe [dependency manifest](lean/lake-manifest.json) pins all ten revisions. The successful run built the fresh project with matching official Mathlib cache objects; it does not claim to rebuild every dependency from source.\n\n'
 block+='Use a clean checkout of the immutable verified revision linked above and a non-root Linux host with the [documented sandbox prerequisites](../../tools/lean/HARNESS.md). From the repository root:\n\n```\n'
 block+='tools/lean/bootstrap.sh /tmp/nla-'+tree+'-check\n'
 block+='tools/lean/selftest.sh /tmp/nla-'+tree+'-check\n'
 block+='tools/lean/verify.sh \\\n  '+cat+'/'+ID+'/lean \\\n  /tmp/nla-'+tree+'-check\n```\n\n'
 block+='The verifier runs the actual controls, statement comparison, permitted-axiom checks and default-kernel replay. Its successful dated logs are linked above. A local `lake build Solution` is a separate development check.\n\n'
 if ID=='RA-08':block+='## Problem statement\n\n'
 text=text.replace(marker,block+marker,1)
 if ID=='MF-16':text=text.replace('**Last checked:** 2026-09-12','**Last checked:** 2026-09-13',1)
 assert text[text.index(marker):]==suffix;(E/'README.md').write_text(text)
 checks=[];A=D/'successful-checks';assert not A.exists();A.mkdir()
 for label,args in [('permanent-ids',['python3','tools/validate_problem_ids.py','--base-ref','origin/main']),('format',['python3','tools/format_math.py','--check']),('render',['python3','tools/render_problems.py',ID]),('diff-check',['git','diff','--check','HEAD'])]:
  run=subprocess.run(args,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log=A/(label+'.log');log.write_bytes(run.stdout);checks.append(dict(command=args,exit_code=run.returncode,log=str(log.relative_to(D)),log_sha256=sha(log)));assert run.returncode==0,(label,run.stdout.decode())
 V=Path('/tmp/nla-lean-formalization/'+tree+'-reproduction-addendum-pages');V.mkdir(exist_ok=True);subprocess.run(['/opt/homebrew/bin/pdftoppm','-scale-to','1400','-png',str(E/'problem.pdf'),str(V/'page')],check=True)
 pdftext=subprocess.check_output(['/opt/homebrew/bin/pdftotext','-layout',str(E/'problem.pdf'),'-']);(D/'pdf-text.txt').write_bytes(pdftext)
 for r,h in prior.items():assert sha(P/r)==h,r
 current={r:sha(R/r) for r in initial};assert {r for r in current if current[r]!=initial[r]}==set(before)
 record=dict(utc=datetime.now(timezone.utc).isoformat(),problem=ID,candidate=C,reason='CONTRIBUTING requires direct canonical exact theorem names, checked versions and reproduction commands; add them without math or Lean-project wrapper edits.',initial_publication_files=initial,current_publication_files=current,before_canonical_files=before,after_canonical_files={r:sha(R/r) for r in before},original_target_suffix_sha256=hashlib.sha256(suffix.encode()).hexdigest(),original_target_suffix_unchanged=True,all_existing_project_files_preserved=prior,proof_or_statement_or_manifest_edits=False,checked_names=names,checks=checks,pdf_images={str(f):sha(f) for f in sorted(V.glob('*.png'))},visual_review='pending actual root and independent display',independent_addendum_review='pending; initial reviews alone do not approve this amendment',marker_scope='Continuation of the already recorded publication operation, no new or retroactive marker claim')
 (D/'ADDENDUM.json').write_text(json.dumps(record,indent=2)+'\n');(D/'prepare.py').write_bytes(Path(__file__).read_bytes());print(json.dumps({'problem':ID,'pages':list(record['pdf_images']),'pdf':sha(E/'problem.pdf'),'tex':sha(E/'problem.tex'),'existing_project_files_preserved':len(prior)},indent=2),flush=True)
