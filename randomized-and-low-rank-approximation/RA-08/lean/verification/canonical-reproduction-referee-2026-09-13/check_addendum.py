"""Read-only RA-08 canonical reproduction addendum review; no Lean/Git mutation."""
from pathlib import Path
import datetime, hashlib, json, re, shlex, shutil, subprocess

E=Path(__file__).resolve().parent
P=E.parents[1]
W=P.parents[2]
D=P/'verification/canonical-reproduction-addendum-2026-09-13'
INITIAL=P/'verification/publication-referee-2026-09-13'
CANDIDATE='de6513d726e3f66d20730fdaef5ba99318ee7e8b'
BASE='5830ed4fb06da0659414a3deb2a40ad327aca052'
PREVIOUS='de6513d726e3f66d20730fdaef5ba99318ee7e8b'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
digest=lambda b:hashlib.sha256(b).hexdigest()
load=lambda p:json.loads(Path(p).read_text())
git=lambda *a:subprocess.check_output(['git',*a],cwd=W)

known={D/'ADDENDUM.json':'1b932e5cac4e325f05bf1a87446bb1ba1e5c6aab853986c4a6e0dbced1d15abe',
 D/'EVIDENCE-MANIFEST.json':'5615d3a45e46f84279f233c90b6960eaa583947c29557670761b1f75483ee26e',
 D/'ROOT-VISUAL-REVIEW.json':'fcab3b03a0aa12aa2d3197449aed335b56dc12c6760258fc2bb0e84f138c354d',
 INITIAL/'EVIDENCE-MANIFEST.json':'3ae6071d1b114e9b36a162c14ae79185f200b35bb5e7c8de5748862a14844efc',
 P/'reviews/publication-referee-2026-09-13.md':'1a263ad6f35e683532a7cc89a289bbce27aaf079986f95699c5e2475481ab545'}
for p,h in known.items():assert sha(p)==h,p
assert git('rev-parse','HEAD').decode().strip()==PREVIOUS
assert git('show','-s','--format=%an%n%ae%n%cn%n%ce',PREVIOUS).decode().splitlines()==['George Stepaniants','','George Stepaniants','']
manifest_counts={}
for directory in [D,INITIAL,P/'verification/publication-2026-09-13',P/'verification/linux-2026-09-12',P/'verification/root-operational-2026-09-12']:
 outer=directory/'EVIDENCE-MANIFEST.json';m=load(outer)
 actual={str(x.relative_to(directory)) for x in directory.rglob('*') if x.is_file() and x!=outer}
 assert actual=={x for x in m['files'] if not x.startswith('../')},directory
 for name,row in m['files'].items():
  p=(directory/name).resolve()
  expected=row if isinstance(row,str) else row['sha256']
  assert sha(p)==expected,p
  if isinstance(row,dict) and 'bytes' in row:assert p.stat().st_size==row['bytes']
 manifest_counts[str(directory.relative_to(P))]={'bound_including_adjacent_report':len(m['files']),'including_outer':len(m['files'])+1,'outer_sha256':sha(outer)}

a=load(D/'ADDENDUM.json');assert a['candidate']==CANDIDATE
prior=a['all_existing_project_files_preserved'];assert len(prior)==1457
for name,h in prior.items():assert sha(P/name)==h,name
current={str(x.relative_to(P)) for x in P.rglob('*') if x.is_file() and not x.is_relative_to(D) and not x.is_relative_to(E)}
assert current==set(prior)
initial=load(INITIAL/'CHECKS.json')
assert a['initial_publication_files']==initial['publication_files']
changed={name for name in a['current_publication_files'] if a['current_publication_files'][name]!=a['initial_publication_files'][name]}
assert changed==set(a['after_canonical_files'])=={'randomized-and-low-rank-approximation/RA-08/'+n for n in ['README.md','problem.tex','problem.pdf']}
assert set(git('diff','--name-only',PREVIOUS).decode().splitlines())==set(a['current_publication_files'])
for name,h in a['current_publication_files'].items():assert sha(W/name)==h,name
for name,h in a['before_canonical_files'].items():
 archive=D/'archive'/Path(name).name
 assert sha(archive)==h==initial['publication_files'][name]
canon=W/'randomized-and-low-rank-approximation/RA-08/README.md'
raw=canon.read_text();old=(D/'archive/README.md').read_text();marker='Let $`n\\ge2`$'
assert raw[raw.index(marker):]==old[old.index(marker):]
assert raw[raw.index(marker):].encode()==marker.encode()+git('show',BASE+':randomized-and-low-rank-approximation/RA-08/README.md').split(marker.encode(),1)[1]
assert digest(raw[raw.index(marker):].encode())==a['original_target_suffix_sha256']
section=raw.split('### Checked declarations, versions and reproduction\n',1)[1].split('## Problem statement',1)[0]
stripped=raw.replace('### Checked declarations, versions and reproduction\n'+section+'## Problem statement\n\n','',1)
assert stripped==old
config=load(P/'comparator.json')
shorts=[n for line in section.splitlines() if line.startswith('- `') for n in re.findall(r'`([^`]+)`',line)]
names=['NLA.RA08.'+n for n in shorts]
assert names==config['theorem_names']==a['checked_names'] and len(names)==14
assert '`NLA.RA08.not_concaveSpectralTransferConjecture`' in section and config['definition_names']==[]
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
deps=load(P/'lake-manifest.json')['packages'];assert len(deps)==10
pins={x['name']:x['rev'] for x in deps}
assert (P/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1'
assert 'Lean **4.33.1**' in section
for name in ['mathlib','leancert']:assert pins[name] in section
assert pins['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474'
assert pins['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926'
block=re.findall(r'```\n(.*?)```',section,re.S);assert len(block)==1
commands=[shlex.split(line) for line in block[0].replace('\\\n','').splitlines() if line.strip()]
assert commands==[['tools/lean/bootstrap.sh','/tmp/nla-ra08-check'],['tools/lean/selftest.sh','/tmp/nla-ra08-check'],['tools/lean/verify.sh','randomized-and-low-rank-approximation/RA-08/lean','/tmp/nla-ra08-check']]
assert 'non-root Linux host' in section and 'clean checkout of the immutable verified revision' in section
tool_inputs={}
for name in ['tools/lean/bootstrap.sh','tools/lean/selftest.sh','tools/lean/verify.sh','tools/lean/harness.py','tools/lean/HARNESS.md','tools/lean/source-lock.json','CONTRIBUTING.md']:
 assert (W/name).read_bytes()==git('show',CANDIDATE+':'+name),name
 tool_inputs[name]=sha(W/name)
assert not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',section)
registry=load(W/'problem_ids.json');assert len(registry)==217
assert (W/'problem_ids.json').read_bytes()==git('show',BASE+':problem_ids.json')
for pid,name in registry.items():
 if pid!='RA-08':assert (W/name).read_bytes()==git('show',BASE+':'+name)
for check in a['checks']:
 assert check['exit_code']==0 and sha(D/check['log'])==check['log_sha256']
visual=load(D/'ROOT-VISUAL-REVIEW.json');assert visual['images']==a['pdf_images']
assert visual['pdf_sha256']==sha(canon.with_name('problem.pdf'))=='a8f766201f71f3d6348170c65c2affee97c62d66f901a461753f64f9ec664686'
assert sha(canon.with_name('problem.tex'))=='418f676bfad8383950339f675c2f6292c3a583dd00d6f3f5f5c5ac594f0bfa34'
(E/'pages').mkdir(exist_ok=True)
for name,h in a['pdf_images'].items():
 p=Path(name);assert sha(p)==h;shutil.copyfile(p,E/'pages'/p.name)
import difflib
(E/'canonical-addendum.patch').write_text(''.join(difflib.unified_diff(old.splitlines(keepends=True),raw.splitlines(keepends=True),fromfile='initial-publication/README.md',tofile='corrected-canonical/README.md')))
(E/'reproduction-commands.txt').write_text(block[0])
result={'verdict':'PASS final canonical reproduction addendum; report records actual visual inspection and role limits','reviewer':'/root/formal_review_standards','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'candidate':CANDIDATE,'initial_publication_commit':None,'current_unpublished_branch_head':PREVIOUS,'role':'Main mathematical coauthor; separate from current publication preparer, no independent mathematical approval','project_files_preserved':1457,'complete_inventories':manifest_counts,'original_target_and_216_other_pages_unchanged':True,'IDs':217,'changed_files':a['after_canonical_files'],'fourteen_names':names,'toolchain':'4.33.1','pins':pins,'commands':commands,'checked_command_source_hashes':tool_inputs,'initial_review_and_evidence_unchanged':True,'three_pages_actually_displayed':[1,2,3],'displayed_images':a['pdf_images'],'all_original_mathematics_and_metadata_unchanged':True,'new_Lean_or_Linux_execution':False,'canonical_or_Git_mutation':False}
(E/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'verdict':'PASS','project_files_preserved':1457,'declarations':14,'pages_displayed':3,'CHECKS_sha256':sha(E/'CHECKS.json')},indent=2))
