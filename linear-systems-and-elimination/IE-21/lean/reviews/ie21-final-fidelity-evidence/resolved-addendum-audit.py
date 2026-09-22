from pathlib import Path
import subprocess,json,hashlib,re,datetime
root=Path(__file__).resolve().parents[5]
r=Path(__file__).resolve().parent
base='cc3028f38f048b0e8afbdb64fc63cdb58ffbcbef'
immutable='1eb284b84ecc0d3c958d022b3e020be7fa111391'
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
h=lambda b:hashlib.sha256(b).hexdigest()
assert git('rev-parse','HEAD').decode().strip()==base
old=git('show',base+':RESOLVED.md');new=(root/'RESOLVED.md').read_bytes()
match=re.search(rb'\*\*IE-21 Lean verification, 2026-09-22\.\*\*.*?\n\n',new,re.S);assert match
addition=match.group();assert new[:match.start()]+new[match.end():]==old
assert b'George Stepaniants' in addition and b'Department of Computing and Mathematical Sciences, California Institute of Technology' in addition
assert b'Matthew J. Colbrook retains the original mathematical proof attribution.' in addition
assert b'@' not in addition and b'External human peer review is not claimed.' in addition
assert git('diff','--name-only',base,'--').decode().splitlines()==['RESOLVED.md']
for link in re.findall(rb'\]\(([^)]+)\)',addition):
 if not link.startswith(b'https://'): assert (root/link.decode()).is_file(),link
package='linear-systems-and-elimination/IE-21/lean/'
proofs=sorted((root/package/'NLA').rglob('*.lean'))+[root/package/'Solution.lean']
for p in proofs:
 rel=p.relative_to(root).as_posix();assert p.read_bytes()==git('show',immutable+':'+rel),rel
sol=(root/package/'Solution.lean').read_text();names=re.findall(r'^#assert_trust kernel (NLA\.IE21\.\w+)$',sol,re.M);assert len(names)==23
run=json.loads((r/'resolved-addendum-ci-run.json').read_text());assert run['conclusion']=='success' and run['status']=='completed' and run['head_sha']==base and run['id']==35786770609
assert run['path']=='.github/workflows/lean-verification.yml'
assert any(pr['number']==314 for pr in run['pull_requests'])
jobs=json.loads((r/'resolved-addendum-ci-jobs.json').read_text());job=next(j for j in jobs if j['name'].startswith('verify (IE-21'))
assert job['conclusion']=='success';assert next(s for s in job['steps'] if s['name']=='Fresh sandboxed statement, axiom and kernel verification')['conclusion']=='success'
log=(r/'resolved-addendum-ci-job.log').read_text()
for s in ['PASS: all three actual Comparator.runBuiltinKernel cases behaved as required','PASS: all five Comparator regressions','Lean default kernel accepts the solution','Your solution is okay!','PASS: fresh Comparator run and all controls.']:
 assert s in log,s
for name in names:
 assert "'"+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log,name
for side in ['Challenge','Solution']:
 lines=[x for x in log.splitlines() if 'Exporting #[' in x and 'NLA.IE21.' in x and 'from '+side in x]
 assert len(lines)==1 and all(n in lines[0] for n in names)
assert 'Built LeanCert.Tactic.Verification' in log
out={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'result':'PASS bounded documentation and retained CI audit','base_commit':base,'immutable_source_commit':immutable,'RESOLVED_before_sha256':h(old),'RESOLVED_after_sha256':h(new),'added_paragraph_sha256':h(addition),'all_prior_RESOLVED_bytes_preserved':True,'tracked_delta_only_RESOLVED':True,'proof_files_equal_immutable_commit':len(proofs),'selected_declarations_checked':23,'ci_run':run,'standalone_checker_controls_job':next(j['conclusion'] for j in jobs if j['name']=='checker-controls'),'explanation':'Standalone checker-controls skipped because harness unchanged; actual controls ran and passed within IE-21 verify job.','retained_ci_files_sha256':{p.name:h(p.read_bytes()) for p in [r/'resolved-addendum-ci-run.json',r/'resolved-addendum-ci-jobs.json',r/'resolved-addendum-ci-job.log']}}
(r/'resolved-addendum-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['ci_run','retained_ci_files_sha256']},indent=2))
