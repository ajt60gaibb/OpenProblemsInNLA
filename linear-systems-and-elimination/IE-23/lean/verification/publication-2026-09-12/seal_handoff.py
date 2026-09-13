"""Seal wrapper/render checks after the three-page visual review."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[2];E=Path(__file__).resolve().parent;W=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
integrity=json.loads((E/'INTEGRITY-CHECKS.json').read_text())
for name,h in integrity['publication_sha256'].items(): assert sha(W/name)==h,name
checks=json.loads((E/'checks.json').read_text());assert len(checks)==11
for row in checks:
 assert row['exit_code']==0 and sha(E/row['log'])==row['sha256'],row['name']
cmd=['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py','linear-systems-and-elimination/IE-23/lean']
r=subprocess.run(cmd,cwd=W,capture_output=True);(E/'manifest-final.log').write_bytes(r.stdout+r.stderr);assert r.returncode==0
assert 'Pages:           3' in (E/'pdfinfo.log').read_text()
assert 'IE-23: OK' in (E/'render.log').read_text()
assert not re.search(r'Overfull|Missing character',(E/'render.log').read_text())
for revision in [integrity['head'],integrity['candidate']]:
 fields=subprocess.check_output(['git','show','-s','--format=%an%x00%ae%x00%cn%x00%ce',revision],cwd=W).rstrip(b'\n').split(b'\0')
 assert fields==[b'George Stepaniants',b'',b'George Stepaniants',b''],revision
visual={'reviewer':'/root/solved_statement_inventory','review_role':'Publication preparer and prior independent mathematical referee1; this is not a new proof or operational review',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'local_date':'2026-09-12 America/New_York',
 'renderer':'Unchanged tools/render_problems.py with Pandoc3.11 and XeLaTeX; two passes',
 'renderer_sha256':sha(W/'tools/render_problems.py'),'pdf_sha256':sha(P.parent/'problem.pdf'),
 'tex_sha256':sha(P.parent/'problem.tex'),'pages':3,
 'render_warnings':'none','inspection':'All three rendered PNG pages viewed. No clipping, overlap, broken glyphs, unreadable references or crowded command block. Page1 holds status, credits and complete export list; page2 preserves the full original target together; page3 retains complete references and dated prior audits. Source paragraph continuation across pages1/2 is legible.',
 'images':{f'page-{i}.png':sha(E/f'page-{i}.png') for i in range(1,4)},
 'PDF_skill_marker':{'script':'/Users/georgestepaniants/.codex/plugins/cache/openai-primary-runtime/pdf/26.904.11930/skills/pdf/container_tools/mark_artifact_operation_started.mjs','operation':'edit','expected_output_count':1,'format':'pdf','observed_exit_code':0,'invocations':1,'before_first_authoring_write':True},
 'final_manifest_command':cmd,'final_manifest_exit':0,'final_manifest_log_sha256':sha(E/'manifest-final.log')}
(E/'VISUAL-REVIEW.json').write_text(json.dumps(visual,indent=2)+'\n')
handoff=f'''# IE-23 publication package - 12 September 2026

**Ready for the coordinator's independent publication review. No publication
commit, push or PR was created by this preparer.** The branch remains at normal
integration `{integrity['head']}`, containing upstream
`{integrity['upstream_base']}`. Both this integration commit and the immutable
candidate record George Stepaniants with empty author and committer emails.

The canonical original uniqueness conjecture is marked **Lean verified** on
the strength of actual Ubuntu run **34725525250** at immutable candidate
`{integrity['candidate']}`. The exact p=4 source witness gives two distinct
global minimizers over every complex right inverse, proving the complete
canonical negative answer. The source's stronger all-p formulas, full
classifications and higher-dimensional families retain their manuscript and
informal-review scope. Genuine induced-supremum, Euclidean/real-power, rank,
inverse and all-competitor semantics remain exactly as verified.

Operational report `de746fa0bc2d1cf905b9275c9f5f233a043d3fdc55f35deda04f9226c6dd216e`
and outer manifest `3d4685d019c85ba80681551637f43ecf8bfc428a91dc8c985596405f36178da2`
bind 330 files plus the manifest itself. Coordinator acceptance
`17f33157d63f994a2389d0ad03beaa9627d7c4275b622f6906c8b64dee2dbd16`
is bound by root manifest
`b35250b043bb8ddf2bbbc5c03c20c771b89c15e91f18f2bc5af5495b0f17abe1`.
These bytes, all original archives and every nested manifest are unchanged.
The accepted run matched all eight exports, replayed the default kernel,
reported sixteen standard-three axiom closures and exercised both real
control suites. Ten dependencies were freshly cloned with8690 official
Mathlib cache files reused; no full dependency-source rebuild is claimed.
Nested Bubblewrap was denied UID-map creation before its inner write.
LeanCert supplies explicit kernel trust auditing of this pure exact proof;
there is no numerical interval certificate.

## Identity and scope

- All **188 non-wrapper inputs among190** remain identical to the actual
  submitted receipt and immutable Git blobs. Both exact prior wrappers are
  archived under `archive/`.
- All **331 Linux evidence files** and **seven coordinator evidence files**
  remain unchanged. The outer inventory includes every nested manifest.
- All103 non-README proof-freeze inputs, the exact historical README archive,
  code, dependency pins, default target, Comparator config, eight exports,
  original source snapshots and all prior review evidence are preserved.
- Exactly five manifest fields change: `status.scope`, `review.status`,
  `review.notes`, `review.linux_verification.status` and
  `review.linux_verification.note`. Remaining metadata is structurally identical.
- Every217 permanent ID/path is unchanged; all other216 canonical pages,
  all prior16 Lean-verified entries and **6967 unaffected upstream files**
  are preserved. The entire original IE-23 problem-statement/reference/audit
  suffix is byte-identical. Only IE-23's existing RESOLVED block changes.
- Exactly nine tracked files change: canonical README/TeX/PDF, the two project
  wrappers, RESOLVED and the root/category/catalog generated indexes.

## Checks and visual review

Origin/main and immutable-upstream ID validators, all17 ID tests, full
catalog regeneration, global math-format checking, actual v0.4 schema and
all-eight-export coverage pass. Branch counts are **17 Lean verified,
75 Solved,53 Open,72 Partially resolved**, totaling217.

The unchanged repository renderer generated the canonical TeX/PDF with no
overfull boxes or missing-character warnings. All **three PDF pages** were
rendered and visually inspected: readable type and links, clean margins,
complete export list and commands, and the entire original mathematical
target together on page2. `VISUAL-REVIEW.json` binds the exact reviewed PDF,
TeX and PNG bytes. No Lean/cache work or new Linux execution occurred.
The successful run remains bound to its original candidate, not these new
publication wrappers.

## Credit and roles

Mathematical resolution: **Matthew J. Colbrook**. Underlying example and
original question: **Ivan Dokmanić and Rémi Gribonval**. Formalization:
**George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA**, with
AI-agent assistance and no email address.

Preparer `/root/solved_statement_inventory` previously served as independent
mathematical referee1; publication packaging is not another proof review.
Operational inspector `/root/leancert_examples` authored the proof. The
coordinator `/root`, independent of that author and previously mathematical
referee2, separately accepted the actual execution evidence. These roles
are disclosed in the public guide and manifest. No external human review,
official Tau Ceti endorsement or priority claim is introduced.

`INTEGRITY-CHECKS.json`, `preserved-upstream-files.json`, `checks.json` and
`VISUAL-REVIEW.json` contain reproduction commands and exact hash bindings.
The outer publication evidence manifest excludes only itself.
The coordinator should inspect the nine-file diff, public wording and all
three PDF pages before committing, pushing and opening the individual PR.
'''
for old,new in [('with8690','with 8690'),('among190','among 190'),('All103','All 103'),('Every217','Every 217'),('other216','other 216'),('prior16','prior 16'),('all17','all 17'),('Solved,53','Solved, 53'),('Open,72','Open, 72'),('totaling217','totaling 217'),('page2','page 2'),('referee1','referee 1'),('referee2','referee 2')]:handoff=handoff.replace(old,new)
(E/'PUBLICATION-HANDOFF.md').write_text(handoff)
files={}
for path in sorted(E.rglob('*')):
 if path.is_file() and path!=E/'EVIDENCE-MANIFEST.json':
  files[str(path.relative_to(E))]={'sha256':sha(path),'bytes':path.stat().st_size}
outer={'scope':'IE23 publication wrappers, exact preservation checks and canonical PDF visual review; no new mathematical or Linux verification',
 'reviewer':'/root/solved_statement_inventory','role':visual['review_role'],
 'candidate':integrity['candidate'],'branch_head':integrity['head'],
 'inventory_rule':'Exclude only this exact outer manifest path; every nested file and manifest is included.',
 'file_count':len(files),'files':files}
(E/'EVIDENCE-MANIFEST.json').write_text(json.dumps(outer,indent=2)+'\n')
for name in ['PUBLICATION-HANDOFF.md','INTEGRITY-CHECKS.json','VISUAL-REVIEW.json','EVIDENCE-MANIFEST.json']:
 print(name,sha(E/name))
for name in ['README.md','formalization.yaml']:
 print('lean/'+name,sha(P/name))
print('canonical README',sha(P.parent/'README.md'))
print('canonical PDF',sha(P.parent/'problem.pdf'))
print('Bound publication files',len(files),'plus outer')
