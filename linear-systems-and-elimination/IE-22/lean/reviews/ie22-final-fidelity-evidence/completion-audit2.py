#!/usr/bin/env python3
"""Independent IE22 completion evidence audit, with publication Git byte binding.
Read-only inputs; writes only this reviewer's additive completion receipts.
"""
from pathlib import Path, PurePosixPath
import datetime, hashlib, json, re, subprocess, tarfile
P=Path(__file__).resolve().parents[2]; R=P.parents[2]; E=P/'verification/linux'; O=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def digest(p):return sha(p.read_bytes())
def read(n):return json.loads((E/n).read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
def check(ok, label):
 if not ok:raise AssertionError(label)
 checks.append(label)
checks=[]
commit='c45f9ccef20a2fa5cc4b988e93d4173dab853362'; prefix=P.relative_to(R).as_posix()
check(prefix=='linear-systems-and-elimination/IE-22/lean','project path exact')
check(digest(E/'OPERATIONAL-REVIEW.md')=='5e7854c7ce6801da27aa87648fa0209adfaec427fcbef69b0ec9c89a3fb8c0cf','frozen operator report hash')
check(digest(E/'evidence-manifest.json')=='a26606cc445414a8532aa1337ca5df6d0cb047dd1b42e416afed9fd8cac2a9e7','frozen evidence manifest hash')
manifest=read('evidence-manifest.json')['files']; check(len(manifest)==455,'455 manifest files')
for n,h in manifest.items():check(digest(E/n)==h,'evidence '+n)
check(set(manifest)=={str(p.relative_to(E)) for p in E.rglob('*') if p.is_file()}-{'evidence-manifest.json'},'manifest complete exact file set')
inputs=read('input-receipt.json'); hashes=inputs['input_sha256']
check(len(hashes)==394,'394 input files')
tree=git('ls-tree','-r','-z',commit,'--',prefix).split(b'\0'); committed={}
for item in filter(None,tree):
 meta,n=item.split(b'\t',1); mode,kind,obj=meta.decode().split(); n=n.decode(); local=str(PurePosixPath(n).relative_to(prefix))
 check(mode in ('100644','100755') and kind=='blob','ordinary committed input '+local)
 check('.lake' not in PurePosixPath(local).parts and PurePosixPath(local).suffix not in {'.olean','.ilean','.o','.so','.a'},'no build input '+local)
 committed[local]=sha(git('cat-file','blob',obj))
check(committed==hashes,'all committed publication blobs equal input receipt')
check({str(p.relative_to(E/'source')):digest(p) for p in (E/'source').rglob('*') if p.is_file()}==committed,'all archived source bytes equal publication commit')
check(git('rev-parse',commit+'^').decode().strip()==inputs['publication_parent'],'publication parent provenance')
check(subprocess.run(['git','merge-base','--is-ancestor',inputs['publication_base'],commit],cwd=R).returncode==0,'publication base ancestry')
check(git('archive','--format=tar',commit,'--',prefix)==(E/'input.tar').read_bytes(),'input archive exactly regenerated from publication Git')
check(digest(E/'input.tar')==inputs['archive_sha256'],'input archive digest')
archive_count={}
for n,expected in [('input.tar',None),('verification-evidence.tar.gz',None)]:
 seen={}
 with tarfile.open(E/n) as ar:
  for m in ar.getmembers():
   path=PurePosixPath(m.name)
   check(not path.is_absolute() and '..' not in path.parts and (m.isfile() or m.isdir()),'safe archive member '+n+':'+m.name)
   if m.isfile():
    check(m.name not in seen,'unique archive member '+n+':'+m.name)
    content=ar.extractfile(m).read(); seen[m.name]=sha(content)
    if n=='verification-evidence.tar.gz':check(content==(E/m.name).read_bytes(),'exported evidence member '+m.name)
  if n=='input.tar':check({str(PurePosixPath(k).relative_to(prefix)):v for k,v in seen.items()}==hashes,'input archive exact member contents')
 archive_count[n]=len(seen)
check(digest(E/'verification-evidence.tar.gz')==read('evidence-export-receipt.json')['sha256'],'evidence archive digest')
for name,key in [('preparation.json','input_sha256'),('input-authentication.json','source_sha256'),('successful-verification/result.json','input_sha256'),('dependency-evidence/dependency-receipt.json','snapshot_input_sha256')]:check(read(name)[key]==hashes,'all394 source binding '+name)
freeze=json.loads((E/'source/reviews/package-source-freeze.json').read_text())['source_sha256']
check(len(freeze)==57,'57 core frozen files')
for n,h in freeze.items():check(hashes[n]==h==digest(P/n),'archived and current core frozen '+n)
check(digest(E/'source/reviews/ie22-final-fidelity-evidence/source-review.md')=='7d66594e418a608bcd7553409f82a54956e72894c63d211890e3b16eb6f8af87','own prior mathematical approval bound')
check(digest(E/'source/reviews/ie22-final-fidelity-evidence/source-receipt.json')=='a134f04cac877be3751aad66b1cb36a4f9f6d45017f360151d44ce16696544d2','own prior source receipt bound')
# Current shared checker is independently bound to input commit and archived checker.
for p in (E/'checker-source').iterdir():
 if p.is_file():check(p.read_bytes()==git('show',commit+':tools/lean/'+p.name),'unchanged shared checker '+p.name)
lock=read('checker-source/source-lock.json'); reference=R/'eigenvalues-and-inverse-problems/IS-03/lean/verification/linux-2026-09-12/source/forsythe'
reference_checks={}
for rec in lock['files']:
 p=reference/rec['destination']
 if p.is_file():
  check(digest(p)==rec['sha256'] and p.stat().st_size==rec['bytes'],'pinned retained comparator reference '+rec['destination'])
  reference_checks[rec['destination']]=rec['sha256']
for n in ['.tools/comparator/Main.lean','.tools/comparator/Comparator/Axioms.lean','.tools/comparator/Comparator/Compare.lean','scripts/strict_landrun.py','reproduction/checks/PinnedReplayProbe.lean','reproduction/checks/run_replay.sh','reproduction/checks/comparator_regressions.py']:check(n in reference_checks,'inspected checker source authenticated '+n)
for rec in lock['files']:
 if rec['destination']=='scripts/strict_landrun.py':check(digest(E/'checker-runtime-source/strict_landrun.py')==rec['sha256'],'actual strict adapter pinned')
boot=read('bootstrap.json'); result=read('successful-verification/result.json'); dep=read('dependency-evidence/dependency-receipt.json')
check(result['tool_receipt']==boot==read('prerequisite-inspection.json')['tool_receipt'],'bootstrap runtime authentication chain')
check(boot['source_lock_sha256']==digest(E/'checker-source/source-lock.json'),'checker source lock digest')
check(boot['ci_sandbox_probe_sha256']==digest(E/'checker-runtime-source/sandbox_probe_ci.py'),'runtime probe digest')
check(boot['env_sha256']==digest(E/'checker-runtime-source/env.sh'),'runtime environment digest')
check(read('environment-repair.json')['policy_sha256']==sha(git('show',commit+':.github/workflows/lean-verification.yml')),'AppArmor prerequisite matches published CI')
packages=json.loads((E/'source/lake-manifest.json').read_text())['packages']; pins={p['name']:(p['url'],p['rev']) for p in packages}
check(len(pins)==10,'ten dependency pins')
check(pins=={p['name']:(p['url'],p['actual_git_head']) for p in dep['packages']},'all ten runtime dependency URLs and heads match')
check(digest(E/'dependency-evidence/LeanCert-Verification.lean')==dep['LeanCert_Verification_sha256']=='2c576708b528acdde17796b0b715b83079f9cad377182dbd87c248323ff0a58c','authentic LeanCert checker byte binding')
# Independently authenticate the preserved actual LeanCert source against local pinned Git.
localcert=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages/leancert')
if (localcert/'LeanCert/Tactic/Verification.lean').is_file():
 check((localcert/'LeanCert/Tactic/Verification.lean').read_bytes()==(E/'dependency-evidence/LeanCert-Verification.lean').read_bytes(),'LeanCert evidence also matches independent local cache bytes; cache has no Git database')
logs={p.name:p.read_text() for p in (E/'successful-verification').glob('*.log')}; proof=logs['comparator.log']; names=inputs['theorem_names']; ax={'propext','Classical.choice','Quot.sound'}
exports=re.findall(r'^Exporting #\[(.*)\] from (Challenge|Solution)$',proof,re.M)
check([mod for _,mod in exports]==['Challenge','Solution'],'two separate ordered exports')
for decls,mod in exports:check([n for n in decls.split(', ') if n.startswith('NLA.IE22.')]==names,'exact20 exported '+mod)
check(proof.index('from Challenge')<proof.index('Building Solution'),'Challenge export precedes Solution build')
reports=re.findall(r"^info: Solution\.lean:\d+:\d+: '([^']+)' depends on axioms: \[([^]]+)\]$",proof,re.M)
check([n for n,_ in reports]==names and all(set(a.split(', '))==ax for _,a in reports),'all20 actual transitive standard3 axiom outputs')
modules={n[:-5].replace('/','.') for n in hashes if n.startswith('NLA/') and n.endswith('.lean')}
check(len(modules)==47 and set(re.findall(r'Built (NLA\.[\w.]+) \(',proof))==modules,'47 distinct fresh NLA builds')
check(len(re.findall(r'^warning: Challenge\.lean:.*declaration uses `sorry`$',proof,re.M))==20 and not re.search(r'^warning: (?!Challenge\.lean:)|^error:',proof,re.M),'only20 deliberate Challenge warnings; no Solution errors or warnings')
check('Built LeanCert.Tactic.Verification' in proof and 'Built Solution' in proof,'authentic LeanCert checker and wrapper compiled')
check(proof.rstrip().endswith('Lean default kernel accepts the solution\nYour solution is okay!\n\nEXIT_STATUS=0'),'actual final kernel/comparator acceptance')
check('No files to download' in logs['mathlib-cache.log'],'explicit upstream retained-cache limit')
for n in ['user-service.log','sandbox.log','kernel-controls.log','comparator-controls.log','dependencies.log','mathlib-cache.log','comparator.log']:check(logs[n].rstrip().endswith('EXIT_STATUS=0'),'actual phase exit0 '+n)
for n,reason in [('negative-sorry.log',"Illegal axiom detected: 'sorryAx'"),('negative-native.log',"Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")]:check(reason in logs[n] and logs[n].rstrip().endswith('EXIT_STATUS=1'),'actual expected rejection '+n)
runner=read('runner-result-attempt-1.json'); check(runner['status']=='finished' and runner['exit_code']==0,'complete runner result exit0')
check(result['repository_commit']==read('preparation.json')['guest_repository_commit']=='3ee64b33ae1c626b3c7ffa1c4e561b6055623bb9' and result['repository_commit']!=commit,'distinct guest commit truthfully identified')
cleanup=P/'reviews/publication/vm-cleanup.json';check(digest(cleanup)=='09213d8441f7b22fa8c57ad4b79c1b0516d3d5ddcaf1eb875361ace7d0b23e90','additive VM cleanup receipt hash')
c=json.loads(cleanup.read_text());check(c['stop_exit_code']==0 and c['final_state']['Running'] is False and c['final_state']['State']=='stopped','separate actual VM stopped receipt')
# Recompute the manifest at the end as well.
check(all(digest(E/n)==h for n,h in manifest.items()),'all455 evidence hashes unchanged at end')
check(all(digest(P/n)==h for n,h in freeze.items()),'all57 frozen current source hashes unchanged at end')
record={'phase':'IE22 independent final fidelity completion evidence audit','reviewer':'/root/ie22_final_fidelity','AI_agent':True,'nonauthor_of_IE22_boundary_proofs_packaging_and_linux_execution':True,'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'publication_input_commit':commit,'guest_verification_commit':result['repository_commit'],'run':'verify-20260922T221554Z-991','all_checks_pass':True,'check_count':len(checks),'checks':checks,'evidence_manifest_sha256':digest(E/'evidence-manifest.json'),'operator_report_sha256':digest(E/'OPERATIONAL-REVIEW.md'),'evidence_files':len(manifest),'input_files':len(hashes),'frozen_core_files':len(freeze),'fresh_modules':len(modules),'selected_declarations':len(names),'archive_member_counts':archive_count,'authenticated_retained_checker_sources':reference_checks,'sha256':{n:digest(E/n) for n in ['audit_evidence.py','input.tar','verification-evidence.tar.gz','successful-verification/result.json','successful-verification/comparator.log','bootstrap.json','dependency-evidence/dependency-receipt.json']},'vm_cleanup_receipt_sha256':digest(cleanup),'reviewer_correction':'Initial additive completion-audit.py assumed the local cached LeanCert directory retained .git; git exit128 preserved in completion-audit.log. Corrected reviewer audit uses local cache byte equality and the authenticated actual Linux Git observer for Git provenance. No source, controls, or evidence changed.',
'limitations':['Reviewed actual operator Linux evidence; did not personally rerun Linux verifier','Upstream dependency oleans came from retained Mathlib cache; all47 project modules freshly built','Temporary Comparator raw streams not retained; no raw stream digest or replay-from-archive claim','Bootstrap binaries authenticated by runtime receipt, not rebuilt by this reviewer','Publication metadata and PR diff remain separate gate']}
(O/'completion-audit-receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['checks','authenticated_retained_checker_sources']},indent=2))
