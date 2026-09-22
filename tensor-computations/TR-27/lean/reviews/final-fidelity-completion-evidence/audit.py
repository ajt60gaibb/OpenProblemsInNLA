#!/usr/bin/env python3
"""Independent final-referee evidence binding; does not execute Lean or Linux."""
from pathlib import Path, PurePosixPath
import hashlib,json,re,subprocess,tarfile

base=Path(__file__).resolve().parents[2]
repo=base.parents[2]
evidence=base/'verification/linux'
publication='775e8b169119c4045b07db7666eda8c001ae3bd1'
project='tensor-computations/TR-27/lean'
def sha(b): return hashlib.sha256(b).hexdigest()
def digest(p): return sha(p.read_bytes())
def unique(pairs):
    result={}
    for k,v in pairs:
        assert k not in result,k
        result[k]=v
    return result
def read(p):return json.loads(p.read_text(),object_pairs_hook=unique)
def git(*args):return subprocess.check_output(['git',*args],cwd=repo)
def archive_map(p,prefix=''):
    result={}
    with tarfile.open(p) as tf:
        for m in tf.getmembers():
            path=PurePosixPath(m.name)
            assert not path.is_absolute() and '..' not in path.parts,m.name
            assert m.isfile() or m.isdir(),m.name
            if not m.isfile():continue
            rel=str(path.relative_to(prefix)) if prefix else str(path)
            assert rel not in result,rel
            result[rel]=sha(tf.extractfile(m).read())
    return result
input_receipt=read(evidence/'input-receipt.json')
result=read(evidence/'successful-verification/result.json')
prep=read(evidence/'preparation.json')
provenance=read(evidence/'execution-provenance.json')
deps=read(evidence/'dependency-evidence/dependency-receipt.json')
old=read(base/'reviews/final-fidelity-source-receipt.json')
config=read(base/'comparator.json')
expected=input_receipt['input_sha256']
assert len(expected)==116
assert input_receipt['publication_commit']==publication
assert result['project']==project
assert result['input_sha256']==expected==prep['input_sha256']==deps['snapshot_input_sha256']
assert result['repository_commit']==prep['guest_repository_commit']==provenance['guest_repository_commit']=='59f8e715525a25cce2e4767a1372a94650c8071c'
assert prep['publication_commit']==provenance['publication_commit']==publication
assert result['result']=='comparator-accepted'
assert result['config']==config
assert prep['uid']==provenance['uid']==1000
names=config['theorem_names']
assert len(names)==len(set(names))==25
assert config['definition_names']==[]
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert archive_map(evidence/'input.tar',project)==expected
assert digest(evidence/'input.tar')==input_receipt['archive_sha256']
assert (evidence/'input.tar').stat().st_size==input_receipt['archive_bytes']
assert {str(p.relative_to(evidence/'source')):digest(p) for p in (evidence/'source').rglob('*') if p.is_file()}==expected
raw=git('ls-tree','-r','-z',publication,'--',project)
blobs={}
for row in raw.split(b'\0'):
    if not row:continue
    meta,path=row.split(b'\t');mode,kind,oid=meta.decode().split()
    assert mode in {'100644','100755'} and kind=='blob'
    rel=str(PurePosixPath(path.decode()).relative_to(project))
    blobs[rel]=sha(git('cat-file','blob',oid))
assert blobs==expected
for name,h in expected.items():
    assert digest(base/name)==h,name
    assert Path(name).suffix not in {'.olean','.ilean','.o','.so','.a'}
    assert '.lake' not in Path(name).parts
for name,h in old['source_sha256'].items():
    assert expected[name]==h,('prior review differs',name)
freeze=read(base/'reviews/statement-freeze.json')
for name in ['NLA/TR27/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md','comparator.json']:
    assert expected[name]==freeze['sha256'][name]
assert digest(base/'reviews/final-fidelity-referee.md')=='8281caf77d7372b8cd8f647e3ef28e9f3fd2cd398020356179664f272c867def'
assert digest(base/'reviews/final-fidelity-source-receipt.json')=='d55240bbca3c33f6d63bbaea493cd5246b1c0c7eb7c765cb4040a093ef2cbc35'
export_receipt=read(evidence/'evidence-export-receipt.json')
assert digest(evidence/'verification-evidence.tar.gz')==export_receipt['sha256']
archive_files=archive_map(evidence/'verification-evidence.tar.gz')
for name,h in archive_files.items():assert digest(evidence/name)==h,('evidence archive differs',name)
log=(evidence/'successful-verification/comparator.log').read_text()
assert 'Building Challenge' in log and 'Building Solution' in log
exports=re.findall(r'^Exporting #\[(.*)\] from (Challenge|Solution)$',log,re.M)
assert [m for _,m in exports]==['Challenge','Solution']
for items,module in exports:assert [x.strip() for x in items.split(',') if x.strip().startswith('NLA.TR27.')]==names,module
axioms=re.findall(r"^info: Solution\.lean:\d+:\d+: '(NLA\.TR27\.\w+)' depends on axioms: \[([^]]*)\]$",log,re.M)
assert [n for n,a in axioms]==names
for n,a in axioms:assert set(a.split(', '))==set(config['permitted_axioms']),n
assert 'Built LeanCert.Tactic.Verification' in log
assert 'Lean default kernel accepts the solution' in log and 'Your solution is okay!' in log
assert log.rstrip().endswith('EXIT_STATUS=0')
assert not re.search(r'warning: Solution|error:|Illegal axiom|kernel rejects',log)
assert len(re.findall(r'warning: Challenge\.lean:.*declaration uses `sorry`',log))==25
s=(base/'Solution.lean').read_text()
assert 'set_option leancert.trust "kernel"' in s
assert re.findall(r'^#assert_trust kernel (\S+)',s,re.M)==names
assert re.findall(r'^#print axioms (\S+)',s,re.M)==names
manifest=read(base/'lake-manifest.json')
assert len(manifest['packages'])==len(deps['packages'])==10
checkoutlog=(evidence/'successful-verification/dependencies.log').read_text()
for package,actual in zip(manifest['packages'],deps['packages']):
    assert package['name']==actual['name']
    assert package['url']==actual['url']
    assert package['rev']==actual['manifest_revision']==actual['actual_git_head']
    assert "checking out revision '"+package['rev']+"'" in checkoutlog
assert digest(evidence/'dependency-evidence/LeanCert-Verification.lean')==deps['LeanCert_Verification_sha256']=='2c576708b528acdde17796b0b715b83079f9cad377182dbd87c248323ff0a58c'
boot=read(evidence/'bootstrap.json')
lock=read(evidence/'checker-source/source-lock.json')
assert result['tool_receipt']==boot
assert digest(repo/'tools/lean/source-lock.json')==digest(evidence/'checker-source/source-lock.json')==result['source_lock_sha256']==boot['source_lock_sha256']
assert boot['forsythe_commit']==lock['commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert lock['lean_toolchain']==boot['lean_toolchain']==(base/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1'
assert 'aarch64-unknown-linux-gnu' in boot['lean_version']
for p in (evidence/'checker-source').iterdir():
    assert digest(p)==sha(git('show',publication+':tools/lean/'+p.name)),p.name
runtime=evidence/'checker-runtime-source'
strict=next(e for e in lock['files'] if e['destination']=='scripts/strict_landrun.py')
assert digest(runtime/'strict_landrun.py')==strict['sha256']
assert digest(runtime/'env.sh')==boot['env_sha256']
assert digest(runtime/'sandbox_probe_ci.py')==boot['ci_sandbox_probe_sha256']
controls={n:(evidence/'successful-verification'/n).read_text() for n in ['kernel-controls.log','comparator-controls.log','negative-sorry.log','negative-native.log','sandbox.log','user-service.log']}
for n in ['kernel-controls.log','comparator-controls.log','sandbox.log','user-service.log']:assert controls[n].rstrip().endswith('EXIT_STATUS=0')
for n in ['negative-sorry.log','negative-native.log']:assert controls[n].rstrip().endswith('EXIT_STATUS=1')
for marker in ['RETURN honest_with_inductives_and_quotients: accepted','RETURN invalid_raw_proof: rejected','RETURN quotient_postcheck_mismatch: rejected']:
    assert marker in controls['kernel-controls.log']
assert len(re.findall(r'^PASS (?:simple_match|simple_mismatch|simple_axiom_issue|simple_kind_mismatch|type_mismatch):',controls['comparator-controls.log'],re.M))==5
assert "Illegal axiom detected: 'sorryAx'" in controls['negative-sorry.log']
assert "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in controls['negative-native.log']
for mode in ['build','export']:assert 'MODE '+mode+': exit=0' in controls['sandbox.log']
for marker in ['PASS user namespace: private','PASS pid namespace: private','PASS mnt namespace: private','PASS net namespace: private','PASS ipc namespace: private','PASS uts namespace: private','PASS AF_UNIX socket creation: denied','PASS effective capabilities: none','PASS no_new_privs: set','PASS nested namespace write attempt: rejected']:
    assert controls['sandbox.log'].count(marker)==2,marker
assert controls['sandbox.log'].count('NEGATIVE ')==4
assert 'Outer and export fixture contents unchanged; only designated build fixture written.' in controls['sandbox.log']
observed={
 'reviewer':'/root/tr27_final_fidelity','role':'independent nonauthor AI referee',
 'publication_commit':publication,'guest_verification_commit':result['repository_commit'],
 'tracked_source_inputs_verified':len(expected),'archive_evidence_files_verified':len(archive_files),
 'input_sha256':expected,'proof_hashes_match_original_source_review':True,
 'frozen_boundary_unchanged':True,'old_referee_report_and_receipt_unchanged':True,
 'all25_challenge_and_solution_exports_match':True,'all25_standard_axiom_closures_checked':True,
 'authentic_leancert_source_hash_checked':True,'dependency_checkout_pins_checked':10,
 'sandbox_and_rejection_log_checks':'passed',
 'performed_by_this_referee':'local read-only evidence/hash/Git/archive/log audit; did not operate Linux run or rerun Lean',
 'evidence_sha256':{str(p.relative_to(evidence)):digest(p) for p in evidence.rglob('*') if p.is_file() and not str(p.relative_to(evidence)).startswith('source/')},
 'result':'PASS'
}
(base/'reviews/final-fidelity-completion-evidence/audit.json').write_text(json.dumps(observed,indent=2)+'\n')
print('PASS: all 116 inputs match publication Git blobs, input archive, retained source, live package, earlier review and Linux input receipts.')
print('PASS: both 25-target exports, 25 standard axiom closures, exact Solution trust assertions, dependency pins and rejection/isolation controls.')
print('PASS: original fidelity report and receipt are byte-identical; no Lean/Linux execution claimed by this audit.')
