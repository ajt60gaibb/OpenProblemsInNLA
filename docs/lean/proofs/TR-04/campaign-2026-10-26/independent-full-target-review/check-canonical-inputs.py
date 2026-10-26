#!/usr/bin/env python3
"""Independent read-only package, exact statement, copies and archive review."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
import yaml
from source_inventory import without_comments
B=Path(__file__).resolve().parent;REPO=B.parents[5];PROJECT=REPO/'tensor-computations/TR-04/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
artifacts={}
def bind(p,h=None):
    assert p.is_file() and not p.is_symlink(),str(p)
    d=sha(p)
    if h is not None:assert d==h,str(p)
    artifacts[str(p.relative_to(REPO))]=d
    return d
c=json.loads((B/'source-lock.json').read_text())
f=REPO/c['canonical_freeze']['path'];bind(f,c['canonical_freeze']['sha256'])
freeze=json.loads(f.read_text());assert len(freeze['inputs'])==205
actual={}
for p in PROJECT.rglob('*'):
    rel=p.relative_to(PROJECT)
    if '.lake' in rel.parts:continue
    assert not p.is_symlink(),str(rel)
    if p.is_file():actual[str(rel)]=bind(p)
assert actual==freeze['inputs']==c['package_inputs']
assert sum(n.endswith('.lean') for n in actual)==190
copylock=json.loads((PROJECT/'proof-source-lock.json').read_text())
assert len(copylock['copies'])==copylock['actual_copied_source_count']==184
assert copylock['actual_proof_source_count']==179 and copylock['actual_canonical_Lean_input_count']==190
shared={r['path'] for r in c['shared_sources']}
assert {r['source'] for r in copylock['copies']}==shared
for r in copylock['copies']:
    assert bind(REPO/r['source'],r['source_sha256'])==bind(REPO/r['destination'],r['destination_sha256'])
    assert (REPO/r['source']).read_bytes()==(REPO/r['destination']).read_bytes()
assert copylock['fixed_program']=='NLA.Proofs.TR04.ttProgram' and copylock['fixed_C']==1000000 and copylock['fixed_k']==5
config=json.loads((PROJECT/'comparator.json').read_text())
assert config=={'challenge_module':'FullChallenge','solution_module':'FullSolution',
 'theorem_names':['candidate_count_le_first_mode','cyclic_window_count_le_first_mode','NLA.TR04.target'],
 'definition_names':[],'permitted_axioms':['propext','Classical.choice','Quot.sound']}
local={n.removesuffix('.lean').replace('/','.'):n for n in actual if n.endswith('.lean')}
def closure(module,seen):
    if module in seen:return
    assert module in local
    seen.add(module)
    for child in re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)\s*$',without_comments((PROJECT/local[module]).read_text()),re.M):
        if child in local:closure(child,seen)
proof=set()
for module in ['FullSolution','Identity','Check']:closure(module,proof)
assert 'Challenge' not in proof and 'FullChallenge' not in proof and len(proof)==188
assert {local[m] for m in proof}==set(local.values())-{'Challenge.lean','FullChallenge.lean'}
for name in ['FullChallenge.lean','FullSolution.lean']:
    text=without_comments((PROJECT/name).read_text())
    assert re.search(r'namespace\s+NLA\.TR04\s+theorem\s+target\s*:\s*NLA\.Statements\.TR04\.Target\s*:=',text)
assert re.search(r'theorem\s+target_eq_reviewed\s*:\s*NLA\.Statements\.TR04\.Target\s*=\s*NLA\.ReviewedStatements\.TR04\.Target\s*:=\s*rfl',without_comments((PROJECT/'Identity.lean').read_text()))
assert len(re.findall(r'\bsorry\b',without_comments((PROJECT/'FullChallenge.lean').read_text())))==1
for n in proof:
    clean=re.sub(r'"(?:\\.|[^"\\])*"','""',without_comments((PROJECT/local[n]).read_text()))
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by)\b|trustCompiler|debug\.skipKernelTC',clean),local[n]
archive=REPO/freeze['original_archive']['path'];bind(archive,freeze['original_archive']['sha256'])
arch=json.loads(archive.read_text());assert len(arch['records'])==25
for r in arch['records']:
    bind(REPO/r['original_path'],r['sha256']);bind(REPO/r['archive_path'],r['sha256'])
    base=subprocess.check_output(['git','show','2b049df5e9b15318987f3fa592b1a7c65a0c0057:'+r['original_path']],cwd=REPO)
    assert hashlib.sha256(base).hexdigest()==r['sha256']
registry=json.loads((REPO/'problem_ids.json').read_text());assert len(registry)==217
assert registry['TR-04']=='tensor-computations/TR-04/README.md'
manifest=json.loads((PROJECT/'lake-manifest.json').read_text())
sharedmanifest=json.loads((REPO/'lean-statements/lake-manifest.json').read_text())
assert len(manifest['packages'])==10
assert {r['name']:r['rev'] for r in manifest['packages']}=={r['name']:r['rev'] for r in sharedmanifest['packages']}
metadata=yaml.safe_load((PROJECT/'formalization.yaml').read_text())
assert metadata['version']=='v0.4' and metadata['status']['whole_problem_verified'] is False
assert metadata['status']['canonical_status']=='not Lean verified' and metadata['status']['challenge_placeholder_count']==1
assert [r['declaration'] for r in metadata['status']['main_results']]==config['theorem_names']
assert metadata['status']['comparator_result']==metadata['status']['authoritative_linux_result']=='pending'
assert not freeze['legacy_arbitrary_unfoldingRank_tr04Statement_claimed_proved']
command=['python3','docs/lean/proofs/TR-04/sync-canonical-proof.py']
p=subprocess.run(command,cwd=REPO,text=True,capture_output=True);assert p.returncode==0,p.stdout+p.stderr
(B/'source-sync-check.log').write_text(p.stdout+p.stderr)
out={'passed':True,'executed_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification',
 'proof_source_authorship':[],'checker_sha256':sha(Path(__file__)),'canonical_input_count':205,'Lean_count':190,
 'shared_copy_count':184,'TR04_proof_module_count':179,'selected_theorems':config['theorem_names'],
 'solution_import_closure_without_either_Challenge':sorted(proof),'original25_live_archive_and_2b_base_exact':True,
 'permanent_registry_count':217,'old_scaffold_not_claimed_proved':True,'fullTarget_statement_and_frozen_reviewed_identity_literal':True,
 'intentional_comparison_placeholder_count':1,'no_holes_or_trust_bypasses_in188_proof_sources':True,
 'pending_metadata_not_authoritative_acceptance':True,'source_sync_command':command,'source_sync_exit_code':p.returncode,
 'source_sync_log_sha256':sha(B/'source-sync-check.log'),'artifact_hashes':artifacts,
 'fresh_kernel_acceptance_from_this_read_only_check':False,'authoritative_Linux_Comparator':False,'proof_source_changes':False}
(B/'canonical-input-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'sha256':sha(B/'canonical-input-review.json'),'artifacts':len(artifacts)}))
