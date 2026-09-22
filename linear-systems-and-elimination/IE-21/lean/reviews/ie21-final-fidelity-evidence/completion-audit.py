#!/usr/bin/env python3
"""Independent retained-evidence audit, not a new Lean/VM execution."""
from pathlib import Path, PurePosixPath
import hashlib, json, re, subprocess, tarfile
R = Path(__file__).resolve().parent
P = R.parents[1]
ROOT = P.parents[2]
E = P / 'verification/linux'
S = E / 'source'
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: json.loads(p.read_text())
PUB='1eb284b84ecc0d3c958d022b3e020be7fa111391'
GUEST='bd72d630841a1660b9f7652d469186c11728925f'
PROJECT='linear-systems-and-elimination/IE-21/lean'
checks=[]
def passed(s): checks.append(s); print('PASS '+s)
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT)
manifest=read(E/'EVIDENCE-MANIFEST.json')
assert len(manifest['files'])==350
assert sha((E/'EVIDENCE-MANIFEST.json').read_bytes())=='e684400fe12bb40fe5b685bdb9ff64241fe8435e30b1ebaf6e0362dec13528ab'
for n,h in manifest['files'].items(): assert sha((E/n).read_bytes())==h,n
assert manifest['files']['OPERATIONAL-REVIEW.md']=='0cab5065c0640257e9b19912a88c7e41807cccf2112f4d814ff316b79cb476f2'
passed('350-file retained evidence manifest and frozen operational report')
records={n:read(E/n) for n in ['input-receipt.json','input-authentication.json','preparation.json','successful-verification/result.json','dependency-evidence/dependency-receipt.json','execution-provenance.json','runner-result-attempt-1.json']}
i=records['input-receipt.json']; a=records['input-authentication.json']; p=records['preparation.json']; v=records['successful-verification/result.json']; d=records['dependency-evidence/dependency-receipt.json']; provenance=records['execution-provenance.json']; run=records['runner-result-attempt-1.json']
expected=i['input_sha256']; assert len(expected)==289
assert all(x==expected for x in [a['source_sha256'],p['input_sha256'],v['input_sha256'],d['snapshot_input_sha256']])
assert i['publication_commit']==a['publication_commit']==p['publication_commit']==run['publication_commit']==PUB
assert p['guest_repository_commit']==v['repository_commit']==run['guest_repository_commit']==GUEST!=PUB
assert git('rev-parse',PUB+'^').decode().strip()==i['publication_base']=='daf313133bfe730c32a266ea85cd9ca0fbe2d5ed'
assert a['receipt_sha256']==p['receipt_sha256']==sha((E/'input-receipt.json').read_bytes())
items=git('ls-tree','-r','-z',PUB,'--',PROJECT).split(b'\0')
git_hashes={}
for entry in items:
 if not entry: continue
 meta,n=entry.split(b'\t'); mode,kind,obj=meta.split();assert mode in [b'100644',b'100755'] and kind==b'blob'
 name=str(PurePosixPath(n.decode()).relative_to(PROJECT))
 assert '.lake' not in PurePosixPath(name).parts and PurePosixPath(name).suffix not in {'.olean','.ilean','.o','.so','.a'}
 git_hashes[name]=sha(git('cat-file','blob',obj.decode()))
assert git_hashes==expected
assert {str(f.relative_to(S)):sha(f.read_bytes()) for f in S.rglob('*') if f.is_file()}==expected
for n,h in expected.items(): assert sha((P/n).read_bytes())==h,n
passed('all 289 exact committed Git blobs equal publication files, retained snapshot and every guest/result hash record; no project build objects')
archives={}
for name in ['input.tar','verification-evidence.tar.gz']:
 contents={}
 with tarfile.open(E/name) as t:
  for item in t:
   q=PurePosixPath(item.name); assert not q.is_absolute() and '..' not in q.parts and (item.isfile() or item.isdir())
   if item.isfile():
    assert item.name not in contents
    contents[item.name]=sha(t.extractfile(item).read())
 archives[name]=contents
assert {str(PurePosixPath(n).relative_to(PROJECT)):h for n,h in archives['input.tar'].items()}==expected
assert sha((E/'input.tar').read_bytes())==i['archive_sha256']=='6b61efee12a30cde167f1e2ac22b1b0662be0324475e37b222e3cd8ee466c6dd'
assert (E/'input.tar').stat().st_size==i['archive_bytes']==1228800
for n,h in archives['verification-evidence.tar.gz'].items(): assert sha((E/n).read_bytes())==h,n
assert sha((E/'verification-evidence.tar.gz').read_bytes())=='ba04ba6bc5973591c25b3fe6729c683d85966d3dac375bbd2083c8e58d1d5853'
assert (E/'verification-evidence.tar.gz').stat().st_size==346734
passed('both archives recomputed; all 289 input archive members and all 326 exported evidence files match retained bytes')
f=read(S/'reviews/package-source-freeze.json'); old=read(R/'review-receipt.json')
assert len(f['source_sha256'])==41
assert sha((S/'reviews/package-source-freeze.json').read_bytes())==old['package_freeze_sha256']==i['package_source_freeze_sha256']=='b4ab97645ec9f8c46c7130aabc4bac48cbab48af0c96d4f454ad58c32a981744'
assert f['source_sha256']==old['reviewed_package_sha256']
for n,h in f['source_sha256'].items(): assert expected[n]==h
assert sha((R/'review-receipt.json').read_bytes())=='495f82e512208699c3eca8dab8826e5257179e7a82f5cd7b4ac17ed0e8b73543'
assert sha((R/'review.md').read_bytes())=='7050cf5d149dcdcb6ec094a1e30c5dd954efff47ed96e9633511e6a043bc2381'
for n,h in old['canonical_sources_sha256'].items(): assert sha((ROOT/n).read_bytes())==h
passed('all 41 previously approved source package bytes and original mathematical sources unchanged; original independent review preserved')
for file in (E/'checker-source').iterdir():
 assert file.is_file()
 assert file.read_bytes()==git('show',PUB+':tools/lean/'+file.name)
 assert file.read_bytes()==git('show',i['publication_base']+':tools/lean/'+file.name)
boot=read(E/'bootstrap.json'); lock=read(E/'checker-source/source-lock.json'); pre=read(E/'prerequisite-inspection.json')
assert v['tool_receipt']==boot==pre['tool_receipt'] and pre['validated_tools']=='PASS'
assert boot['source_lock_sha256']==v['source_lock_sha256']==sha((E/'checker-source/source-lock.json').read_bytes())
assert boot['forsythe_commit']==lock['commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert boot['lean_toolchain']==(S/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1'
assert boot['env_sha256']==sha((E/'checker-runtime-source/env.sh').read_bytes())
assert boot['ci_sandbox_probe_sha256']==sha((E/'checker-runtime-source/sandbox_probe_ci.py').read_bytes())
strict=next(x for x in lock['files'] if x['destination']=='scripts/strict_landrun.py')
assert strict['sha256']==sha((E/'checker-runtime-source/strict_landrun.py').read_bytes())
for n,h in pre['driver_sha256'].items(): assert sha((E/'checker-source'/n).read_bytes())==h
repair=read(E/'environment-repair.json')
assert repair['policy_sha256']==sha(git('show',PUB+':'+repair['policy_source']))
assert p['uid']==provenance['uid']==1000 and p['prior_project_build_artifacts'] is False
assert p['git_status']==provenance['git_status_after_verification']==''
assert provenance['failed_verification_attempts']==0 and provenance['all_inputs_unchanged_after_verification']
assert run['exit_code']==0 and run['status']=='finished' and v['result']=='comparator-accepted'
passed('unchanged published shared harness; locked runtime receipts; documented Linux prerequisite; distinct clean guest commit and first actual run exit 0')
pins={p['name']:(p['url'],p['rev']) for p in read(S/'lake-manifest.json')['packages']}
assert len(pins)==10
assert {p['name']:(p['url'],p['actual_git_head']) for p in d['packages']}==pins
assert all(p['actual_git_head']==p['manifest_revision'] for p in d['packages'])
assert d['LeanCert_Verification_bytes_match_pinned_git_blob'] is True
assert d['LeanCert_Verification_sha256']==sha((E/'dependency-evidence/LeanCert-Verification.lean').read_bytes())=='2c576708b528acdde17796b0b715b83079f9cad377182dbd87c248323ff0a58c'
passed('all 10 actual dependency Git HEAD observations match immutable manifest; authentic LeanCert verification file retained')
config=read(S/'comparator.json'); names=config['theorem_names']; std={'propext','Classical.choice','Quot.sound'}
assert len(names)==len(set(names))==23 and config==v['config'] and config['definition_names']==[] and set(config['permitted_axioms'])==std
solution=(S/'Solution.lean').read_text(); challenge=(S/'Challenge.lean').read_text()
assert 'set_option leancert.trust "kernel"' in solution and 'import LeanCert.Tactic.Verification' in solution
assert re.findall(r'^#assert_trust kernel (\S+)$',solution,re.M)==names
assert re.findall(r'^#print axioms (\S+)$',solution,re.M)==names
assert ['NLA.IE21.'+n for n in re.findall(r'^theorem (\w+)',challenge,re.M)]==names
log=(E/'successful-verification/comparator.log').read_text()
exports=re.findall(r'^Exporting #\[(.*)\] from (\w+)$',log,re.M)
assert [m for _,m in exports]==['Challenge','Solution']
for ns,m in exports: assert [n for n in ns.split(', ') if n.startswith('NLA.IE21.')]==names
axioms=re.findall(r"^info: Solution.lean:\d+:\d+: '([^']+)' depends on axioms: \[([^]]+)\]$",log,re.M)
assert [n for n,_ in axioms]==names and all(set(a.split(', '))==std for _,a in axioms)
assert len(re.findall(r'^warning: Challenge.lean:.*declaration uses `sorry`$',log,re.M))==23
assert not re.search(r'^warning: (?!Challenge.lean:)|^error:',log,re.M)
modules=[f.stem for f in (S/'NLA/IE21').glob('*.lean')];assert len(modules)==31
for m in modules: assert 'Built NLA.IE21.'+m+' (' in log
for marker in ['Built LeanCert.Tactic.Verification','Built Solution','Running Lean default kernel on solution.','Lean default kernel accepts the solution','Your solution is okay!']:assert marker in log
passed('31 fresh IE21 modules; authentic LeanCert plus all 23 kernel assertions; separate 23-target exports; exact standard-three axiom closure; actual kernel accepted')
logs={f.name:f.read_text() for f in (E/'successful-verification').glob('*.log')}
for n,s in logs.items(): assert s.rstrip().endswith('EXIT_STATUS='+('1' if n.startswith('negative-') else '0')),n
assert "Illegal axiom detected: 'sorryAx'" in logs['negative-sorry.log']
assert "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in logs['negative-native.log']
for marker in ['RETURN honest_with_inductives_and_quotients: accepted','RETURN invalid_raw_proof: rejected','RETURN quotient_postcheck_mismatch: rejected','PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:assert marker in logs['kernel-controls.log']
for case in ['simple_match','simple_mismatch','simple_axiom_issue','simple_kind_mismatch','type_mismatch']:assert 'PASS '+case+':' in logs['comparator-controls.log']
sandbox=logs['sandbox.log']
for m in ['build','export']:assert 'MODE '+m+': exit=0' in sandbox
for marker in ['PASS outside .lake write-open: denied','PASS symlink from .lake to outside write: denied','PASS user namespace: private','PASS pid namespace: private','PASS mnt namespace: private','PASS net namespace: private','PASS ipc namespace: private','PASS uts namespace: private','PASS host parent: absent from private /proc','PASS host parent signal lookup: denied','PASS host loopback listener: unreachable','PASS AF_UNIX socket creation: denied','PASS effective capabilities: none','PASS no_new_privs: set','bwrap: setting up uid map: Permission denied']:assert sandbox.count(marker)==2,marker
for label in ['unknown option','unexpected --rw','unexpected --rwx','relative --rwx']:assert 'NEGATIVE '+label+': exit=2' in sandbox
assert 'PASS build .lake write: allowed' in sandbox and 'PASS export .lake write-open: denied' in sandbox
assert 'No files to download' in logs['mathlib-cache.log']
passed('all real sandbox, three raw-kernel, five comparator and two forbidden-axiom controls; upstream cached-object limitation retained')
print('RESULT: PASS independent retained-evidence audit; no new Linux/Lean execution')
