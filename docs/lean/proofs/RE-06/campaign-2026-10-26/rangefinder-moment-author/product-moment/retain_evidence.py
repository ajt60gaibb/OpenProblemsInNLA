from pathlib import Path
import json,hashlib,shutil,subprocess,datetime
b=Path('/private/tmp/nla-re06-gaussian-dev');r=b/'product-moment-replay'
d=Path('/Users/ajt253/Documents/OpenProblemsInNLA/reviews/2026-10-23-solved-lean/re06-gaussian-product-moment');d.mkdir(exist_ok=False)
w=Path('/Users/ajt253/.codex/worktrees/re06-nonadaptive-oct26/OpenProblemsInNLA/lean-statements')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=next(p for p in sorted((r/'attempts').iterdir(),reverse=True) if (p/'result.json').exists());rs=json.loads((a/'result.json').read_text());assert len(rs)==5
for q in rs:
 assert q['exit_code']==0 and 'warning:' not in q['stdout']+q['stderr'] and 'sorryAx' not in q['stdout']+q['stderr']
 rel=Path(q['module'].replace('.','/')+'.lean');assert sha(r/'source'/rel)==q['sha256']==sha(w/rel)
 out=d/'sources'/rel;out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(r/'source'/rel,out)
shutil.copytree(a,d/'fresh-closure-attempts'/a.name)
for p in (b/'attempts').iterdir():
 if any((p/(m+'.lean')).exists() for m in ['NLA.Proofs.RE06.GaussianProductMoment','NLA.Proofs.RE06.GaussianProductMomentTransport']):shutil.copytree(p,d/'author-attempts'/p.name)
pf=json.loads((b/'residual-replay/CLOSURE_PREFLIGHT.json').read_text())
for dep in pf['dependency_heads']:
 assert subprocess.check_output(['git','-C',dep['path'],'rev-parse','HEAD'],text=True).strip()==dep['expected']
assert sha(Path(pf['lean']))==pf['lean_binary_sha256']
assert sha(r/'compile.py')==pf['compiler_sha256']
shutil.copyfile(b/'residual-replay/CLOSURE_PREFLIGHT.json',d/'CLOSURE_PREFLIGHT.json');shutil.copyfile(r/'compile.py',d/'compile.py');shutil.copyfile(Path(__file__),d/'retain_evidence.py')
receipt=dict(role='Author local macOS kernel evidence only; not independent review, Linux CI, Comparator or full Target evidence',timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Exact actual finite Gaussian two-sided matrix second moment, integrability, HasLaw/original-stream transports, measurable-dependent-factor Fubini and independent parameter transports',source_count=5,initial_project_object_directory_empty=True,fresh_closure_attempt=str(a),kernel_mode=True,permitted_axioms=['propext','Classical.choice','Quot.sound'],new_modules_warning_free=True,modules=[{k:q[k] for k in ['module','sha256','argv','exit_code']} for q in rs],dependency_heads_unchanged_after=True,full_target_claimed=False,public_extra_assumptions_added=False)
(d/'AUTHOR_KERNEL_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');(b/'FROZEN_GAUSSIAN_PRODUCT_MOMENT.json').write_text(json.dumps(receipt,indent=2)+'\n')
(d/'README.md').write_text('''Author local macOS Lean 4.33.1 kernel acceptance for the exact finite-product Gaussian moment `E ||U Z V||_F² = ||U||_F² ||V||_F²`, including all rectangular and empty dimensions. Integrability is proved, and actual HasLaw/original-stream transports are provided. The dependent-factor Fubini helper allows both fixed factors to depend measurably on one independent source parameter; its explicit integrability premise is the resulting coefficient energy product. No frozen public export gains a premise.\n\nAll five project sources were rebuilt in an initially empty project object tree against the pinned read-only dependencies. Every compiled source byte matches the managed worktree. Both new modules are warning-free; every new theorem has a kernel trust assertion and prints only the standard three axioms. All failed author attempts remain diagnostic data. This is not independent review, Linux CI, Comparator evidence or full RE06 Target evidence.\n''')
files=sorted(p for p in d.rglob('*') if p.is_file() and p.name!='SHA256SUMS');(d/'SHA256SUMS').write_text(''.join(f'{sha(p)}  {p.relative_to(d)}\n' for p in files))
print(json.dumps(dict(path=str(d),receipt_sha256=sha(d/'AUTHOR_KERNEL_RECEIPT.json')),indent=2))
