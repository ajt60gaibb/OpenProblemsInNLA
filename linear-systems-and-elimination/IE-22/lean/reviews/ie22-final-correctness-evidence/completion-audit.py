#!/usr/bin/env python3
"""Independent nonauthor audit of the frozen IE22 operational evidence.
This checks retained bytes and execution records; it does not rerun Linux Lean.
"""
from pathlib import Path, PurePosixPath
import datetime, hashlib, json, re, subprocess, tarfile
P=Path(__file__).resolve().parents[2]; E=P/'verification/linux'; R=P.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
file_sha=lambda p:sha(p.read_bytes())
def data(p):
 def unique(xs):
  out={}
  for k,v in xs:
   assert k not in out, ('duplicate JSON key',p,k)
   out[k]=v
  return out
 return json.loads(p.read_text(),object_pairs_hook=unique)
def git(*args): return subprocess.check_output(['git','-C',str(R),*args])
def bind(path,expected): assert file_sha(path)==expected,(str(path),file_sha(path),expected)
expected_manifest='a26606cc445414a8532aa1337ca5df6d0cb047dd1b42e416afed9fd8cac2a9e7'
expected_report='5e7854c7ce6801da27aa87648fa0209adfaec427fcbef69b0ec9c89a3fb8c0cf'
bind(E/'evidence-manifest.json',expected_manifest); bind(E/'OPERATIONAL-REVIEW.md',expected_report)
manifest=data(E/'evidence-manifest.json')['files']; assert len(manifest)==455
for n,h in manifest.items(): bind(E/n,h)
assert {str(p.relative_to(E)) for p in E.rglob('*') if p.is_file()}==set(manifest)|{'evidence-manifest.json'}
I=data(E/'input-receipt.json'); H=I['input_sha256']; assert len(H)==394
commit='c45f9ccef20a2fa5cc4b988e93d4173dab853362'
guest='3ee64b33ae1c626b3c7ffa1c4e561b6055623bb9'
project='linear-systems-and-elimination/IE-22/lean'
assert I['publication_commit']==commit and I['project_path']==project
assert git('rev-parse',commit+'^').decode().strip()==I['publication_parent']
tracked={}
for line in git('ls-tree','-r','-z',commit,'--',project).split(b'\0'):
 if not line: continue
 meta,n=line.split(b'\t',1); mode,kind,obj=meta.decode().split()
 assert kind=='blob' and mode in ('100644','100755')
 name=str(PurePosixPath(n.decode()).relative_to(project))
 assert not any(x in PurePosixPath(name).parts for x in ['.lake'])
 assert PurePosixPath(name).suffix not in {'.olean','.ilean','.o','.so','.a'}
 tracked[name]=sha(git('cat-file','blob',obj))
assert tracked==H
for n,h in H.items(): bind(E/'source'/n,h); bind(P/n,h)
def archive_hashes(path,prefix=''):
 result={}
 with tarfile.open(path) as t:
  for m in t.getmembers():
   name=PurePosixPath(m.name)
   assert not name.is_absolute() and '..' not in name.parts and (m.isdir() or m.isfile())
   if not m.isfile(): continue
   key=str(name.relative_to(prefix)) if prefix else str(name)
   assert key not in result
   result[key]=sha(t.extractfile(m).read())
 return result
assert archive_hashes(E/'input.tar',project)==H
assert (E/'input.tar').stat().st_size==I['archive_bytes']==1597440
bind(E/'input.tar',I['archive_sha256']); assert I['archive_sha256']=='eb5dc854bca9aa8025c0db4af0f3e0538ffba4d262b68dcaf08616dbb62d6931'
assert data(E/'input-authentication.json')['source_sha256']==H
assert data(E/'preparation.json')['input_sha256']==H
prep=data(E/'preparation.json'); assert prep['guest_repository_commit']==guest and prep['git_status']=='' and not prep['prior_project_build_artifacts']
result=data(E/'successful-verification/result.json'); assert result['input_sha256']==H
assert result['repository_commit']==guest and result['project']==project and result['result']=='comparator-accepted'
D=data(E/'dependency-evidence/dependency-receipt.json'); assert D['snapshot_input_sha256']==H
freeze=data(P/'reviews/package-source-freeze.json')['source_sha256']; assert len(freeze)==57
freeze_sha='2a07dedc9ca3774cd9fc5a760f421dd47f105cc257c770f401ae73513dea1226'
bind(P/'reviews/package-source-freeze.json',freeze_sha)
assert I['package_source_freeze_sha256']==freeze_sha
for n,h in freeze.items(): assert H[n]==h
proof=data(P/'reviews/proof-source-freeze.json'); assert len(proof['source_sha256'])==47
for n,h in proof['source_sha256'].items(): assert H[n]==h
assert proof['mathematical_boundary_sha256']==data(P/'reviews/statement-freeze.json')['mathematical_boundary_sha256']
assert len(proof['mathematical_boundary_sha256'])==4
for n,h in proof['mathematical_boundary_sha256'].items(): assert H[n]==h
source_review_sha='3c21b611c77fae39425a7761b0143702bdb381842a576a4e74b6557a5301ab46'
bind(P/'reviews/ie22-final-correctness-evidence/source-review.md',source_review_sha)
bind(P/'reviews/ie22-final-correctness-evidence/final-source-review-receipt.json','fd6c9f4a6d40c802f4afd9e2a72a7ebc2afca61aa382e563e76e7487db063f62')
archive=archive_hashes(E/'verification-evidence.tar.gz'); assert len(archive)==431
for n,h in archive.items(): bind(E/n,h)
bind(E/'verification-evidence.tar.gz','88b84a1785e98114095ab9f74e2ecc4ad6f875f3a812ca6f197c93d62fef04b2')
assert (E/'verification-evidence.tar.gz').stat().st_size==425560
for n,entry in data(E/'transport-receipt.json')['files'].items():
 bind(E/n,entry['sha256']); assert (E/n).stat().st_size==entry['bytes']
config=data(P/'comparator.json'); names=config['theorem_names']; assert len(names)==len(set(names))==20
assert config==result['config'] and names==I['theorem_names'] and not config.get('definition_names',[])
standard={'propext','Classical.choice','Quot.sound'}; assert set(config['permitted_axioms'])==standard
solution=(P/'Solution.lean').read_text(); challenge=(P/'Challenge.lean').read_text()
assert 'import LeanCert.Tactic.Verification' in solution and 'set_option leancert.trust "kernel"' in solution
assert re.findall(r'^#assert_trust kernel (\S+)$',solution,re.M)==names
assert re.findall(r'^#print axioms (\S+)$',solution,re.M)==names
assert ['NLA.IE22.'+n for n in re.findall(r'^theorem (\w+)',challenge,re.M)]==names
assert not re.search(r'^import Challenge\b',solution,re.M)
log=(E/'successful-verification/comparator.log').read_text()
exports=re.findall(r'^Exporting #\[(.*)\] from (Challenge|Solution)$',log,re.M)
assert [m for _,m in exports]==['Challenge','Solution']
for declarations,module in exports:
 assert [n.strip() for n in declarations.split(',') if n.strip().startswith('NLA.IE22.')]==names
assert log.index('from Challenge')<log.index('Building Solution')<log.index('from Solution')<log.index('Running Lean default kernel on solution.')
closures=re.findall(r"^info: Solution.lean:\d+:\d+: '(NLA\.IE22\.[^']+)' depends on axioms: \[([^\]]*)\]$",log,re.M)
assert [n for n,_ in closures]==names
assert all(set(a.split(', '))==standard for _,a in closures)
built=re.findall(r'Built (NLA\.IE\d+\.\w+) \(',log)
expected_built={n[:-5].replace('/','.') for n in proof['source_sha256']}
assert set(built)==expected_built and len(built)==47
warnings=re.findall(r'^warning: (.*)$',log,re.M)
assert len(warnings)==20 and all(re.fullmatch(r'Challenge\.lean:\d+:8: declaration uses `sorry`',w) for w in warnings)
assert not re.search(r'^error:',log,re.M)
for marker in ['Built LeanCert.Tactic.Verification','Built Solution','Lean default kernel accepts the solution','Your solution is okay!','EXIT_STATUS=0']: assert marker in log
assert 'COMPARATOR_LANDRUN=/home/admin/nla-lean-tools/scripts/strict_landrun.py' in log
assert "'RestrictAddressFamilies=~AF_UNIX'" in log
export_receipt=data(E/'export-receipt.json'); assert export_receipt['source_sha256']==sha(log.encode())
packages=data(P/'lake-manifest.json')['packages']; assert len(packages)==10
assert {p['name']:(p['url'],p['rev']) for p in packages}=={p['name']:(p['url'],p['actual_git_head']) for p in D['packages']}
assert all(p['actual_git_head']==p['manifest_revision'] for p in D['packages'])
assert D['package_heads_all_match_manifest'] and D['LeanCert_Verification_bytes_match_pinned_git_blob']
bind(E/'dependency-evidence/LeanCert-Verification.lean','2c576708b528acdde17796b0b715b83079f9cad377182dbd87c248323ff0a58c')
for p in packages: assert f"checking out revision '{p['rev']}'" in (E/'successful-verification/dependencies.log').read_text()
cache=(E/'successful-verification/mathlib-cache.log').read_text(); assert 'Decompressing 8689 already-cached file(s)' in cache and 'No files to download' in cache
for p in (E/'checker-source').iterdir():
 assert p.read_bytes()==git('show',commit+':tools/lean/'+p.name)
B=data(E/'bootstrap.json'); assert result['tool_receipt']==B
bind(E/'checker-source/source-lock.json',B['source_lock_sha256'])
assert B['source_lock_sha256']=='b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b'
lock=data(E/'checker-source/source-lock.json'); assert lock['commit']==B['forsythe_commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62'
strict=next(x for x in lock['files'] if x['destination']=='scripts/strict_landrun.py')
bind(E/'checker-runtime-source/strict_landrun.py',strict['sha256'])
bind(E/'checker-runtime-source/env.sh',B['env_sha256']); bind(E/'checker-runtime-source/sandbox_probe_ci.py',B['ci_sandbox_probe_sha256'])
prereq=data(E/'prerequisite-inspection.json'); assert prereq['validated_tools']=='PASS' and prereq['tool_receipt']==B
for n,h in prereq['driver_sha256'].items(): bind(E/'checker-source'/n,h)
sandbox=(E/'successful-verification/sandbox.log').read_text()
for mode in ['build','export']: assert f'MODE {mode}: exit=0' in sandbox
for marker in ['user namespace: private','pid namespace: private','mnt namespace: private','net namespace: private','ipc namespace: private','uts namespace: private','host parent: absent from private /proc','host parent signal lookup: denied','host loopback listener: unreachable','AF_UNIX socket creation: denied','effective capabilities: none','no_new_privs: set','nested namespace write attempt: rejected exit=1','outside .lake write-open: denied','symlink from .lake to outside write: denied']:
 assert sandbox.count('PASS '+marker)==2,marker
for marker in ['build .lake write: allowed','export .lake write-open: denied','export .lake truncate: denied']: assert 'PASS '+marker in sandbox
for case in ['unknown option','unexpected --rw','unexpected --rwx','relative --rwx']: assert f'NEGATIVE {case}: exit=2' in sandbox
kernel=(E/'successful-verification/kernel-controls.log').read_text()
assert 'RETURN honest_with_inductives_and_quotients: accepted' in kernel
assert 'RETURN invalid_raw_proof: rejected:' in kernel and '(kernel) declaration type mismatch' in kernel
assert 'RETURN quotient_postcheck_mismatch: rejected: Quotient constant mismatch on: Quot.lift' in kernel
controls=(E/'successful-verification/comparator-controls.log').read_text()
expected_controls={'simple_match':(0,'Your solution is okay!'),'simple_mismatch':(1,"Challenge and solution constant kind don't match: 'comm'"),'simple_axiom_issue':(1,"Illegal axiom detected: 'helper'"),'simple_kind_mismatch':(1,"Illegal axiom detected: 'helper'"),'type_mismatch':(1,"Challenge and solution theorem statement do not match: 'checked'")}
for name,(code,marker) in expected_controls.items(): assert f'PASS {name}: exit {code}, expected {code}; required phase: {marker}' in controls
assert len(re.findall(r'^PASS \w+:',controls,re.M))==5
for f,marker in [('negative-sorry.log',"Illegal axiom detected: 'sorryAx'"),('negative-native.log',"Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")]:
 t=(E/'successful-verification'/f).read_text(); assert marker in t and t.endswith('EXIT_STATUS=1\n')
for f in ['user-service.log','sandbox.log','kernel-controls.log','comparator-controls.log','dependencies.log','mathlib-cache.log','comparator.log']: assert (E/'successful-verification'/f).read_text().endswith('EXIT_STATUS=0\n')
run=data(E/'runner-result-attempt-1.json'); assert run['exit_code']==0 and run['publication_commit']==commit and run['guest_repository_commit']==guest
assert run['verification_log_directories']==['/home/admin/nla-lean-tools/logs/verify-20260922T221554Z-991']
assert len(list(E.glob('runner-result-attempt-*.json')))==1
provenance=data(E/'execution-provenance.json'); assert provenance['uid']==1000 and provenance['git_status_after_verification']==''
assert provenance['failed_verification_attempts']==0 and provenance['all_inputs_unchanged_after_verification']
assert provenance['publication_commit']==commit and provenance['guest_repository_commit']==guest
cleanup=P/'reviews/publication/vm-cleanup.json'
if cleanup.exists(): bind(cleanup,'09213d8441f7b22fa8c57ad4b79c1b0516d3d5ddcaf1eb875361ace7d0b23e90')
# Rebind after all inspection; no retained inputs or reports were altered by this audit.
for n,h in manifest.items(): bind(E/n,h)
bind(E/'evidence-manifest.json',expected_manifest)
record={'verdict':'PASS independent retained-evidence audit','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/ie22_final_correctness, nonauthor','publication_source_commit':commit,'guest_verification_commit':guest,'run':'verify-20260922T221554Z-991','operational_report_sha256':expected_report,'evidence_manifest_sha256':expected_manifest,'manifest_bound_files':len(manifest),'archive_bound_files':len(archive),'immutable_git_input_files':len(H),'frozen_core_files':len(freeze),'fresh_project_modules':len(built),'selected_exact_targets':len(names),'permitted_axioms':sorted(standard),'dependency_pin_count':len(packages),'earlier_source_review_sha256':source_review_sha,'audit_script_sha256':file_sha(Path(__file__)),'limits':['Independent retained Linux evidence audit, not a second Linux execution','Upstream Mathlib cache reused; no whole-library source rebuild','Raw Comparator streams deleted by pinned tool; only authenticated logged export lists retained','Later publication metadata/canonical changes require separate review']}
(P/'reviews/ie22-final-correctness-evidence/completion-audit-receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
