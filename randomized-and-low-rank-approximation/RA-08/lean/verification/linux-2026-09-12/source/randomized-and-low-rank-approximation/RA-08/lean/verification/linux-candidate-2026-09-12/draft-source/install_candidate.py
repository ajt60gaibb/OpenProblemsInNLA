"""Authorized one-time installation of the checked RA-08 candidate wrappers.

Retains exact historical files, every proof byte and every raw review input.
No commit, push, Lean command, dependency action or status change is performed.
The layout adapts the retained IS-03 candidate packaging protocol.
"""
from pathlib import Path
import datetime, hashlib, json, os, subprocess

D=Path(__file__).resolve().parent
P=Path('/tmp/nla-lean-ra08-worktree/randomized-and-low-rank-approximation/RA-08/lean')
W=P.parents[2]
E=P/'verification/linux-candidate-2026-09-12'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
excluded_dirs={'.lake','.verification','__pycache__'}
excluded_suffixes={'.olean','.ilean','.trace','.pyc'}
def eligible():
    result=[]
    for parent,dirs,files in os.walk(P):
        dirs[:]=sorted(d for d in dirs if d not in excluded_dirs)
        for name in sorted(files):
            p=Path(parent)/name
            if p.suffix in excluded_suffixes:continue
            assert p.is_file() and not p.is_symlink(),p
            result.append(p)
    return sorted(result)

assert not E.exists(),'Candidate packaging already started; do not overwrite the baseline.'
plan=json.loads((D/'ARCHIVE-AND-INSTALL-PLAN.json').read_text())
checks=json.loads((D/'DRAFT-CHECKS.json').read_text())
assert checks['verdict'].startswith('PASS external-only')
assert sha(D/'README.md')==plan['draft_readme_sha256']
assert sha(D/'formalization.yaml')==plan['draft_metadata_sha256']
acc=P/'verification/final-review-acceptance.json'
assert sha(acc)=='ab7c97b219b098a9d6e1f72cad49e21d68a1ac37cd73f600d971aca5977de84d'
proof=json.loads((P/'verification/proof-freeze.json').read_text())
statement=json.loads((P/'reviews/statement-freeze.json').read_text())
for f in (proof,statement):
    for n,h in f['files'].items():assert sha(P/n)==h,n
    for n,h in f['source_files'].items():
        raw=subprocess.check_output(['git','-C',str(W),'show',f['base']+':'+n])
        assert hashlib.sha256(raw).hexdigest()==h and (W/n).read_bytes()==raw,n
assert not subprocess.check_output(['git','-C',str(W),'diff','--name-only'])
assert not subprocess.check_output(['git','-C',str(W),'diff','--cached','--name-only'])
originals={str(p.relative_to(P)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in eligible()}
manifests={}
for path in P.rglob('EVIDENCE-MANIFEST.json'):
    j=json.loads(path.read_text())
    for rel,row in j['files'].items():
        x=(path.parent/rel).resolve()
        assert x.is_relative_to(P.resolve()) and sha(x)==row['sha256']
        assert x.stat().st_size==row['bytes']
    manifests[str(path.relative_to(P))]={'sha256':sha(path),'bytes':path.stat().st_size,'bound_files':len(j['files'])}
baseline={
    'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'base':subprocess.check_output(['git','-C',str(W),'rev-parse','HEAD'],text=True).strip(),
    'original_project_inputs':originals,'original_project_input_count':len(originals),
    'all_existing_evidence_manifests':manifests,
    'registry_sha256':sha(W/'problem_ids.json'),
    'proof_freeze_sha256':sha(P/'verification/proof-freeze.json'),
    'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),
    'coordinator_acceptance_sha256':sha(acc),
    'archive_plan':plan,'draft_checks_sha256':sha(D/'DRAFT-CHECKS.json'),
    'explicit_parent_authorization':('After draft schema/coverage passes, archive exact historical README and '
        'formalization.yaml, install live truthful wrappers and seal actual candidate packaging with complete '
        'inventory/checks/handoff; no math edits, commit or push. Parent message following final-review '
        'acceptance ab7c97b219b098a9d6e1f72cad49e21d68a1ac37cd73f600d971aca5977de84d.'),
    'role':'/root/leancert_examples, prior independent final referee 1, now separate documentation preparer; no additional mathematical approval',
}
E.mkdir()
(E/'baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
for row in plan['archives_required_before_any_live_replacement']:
    source=P/row['source']; archive=P/row['archive']
    assert sha(source)==row['sha256'] and not archive.exists()
    archive.write_bytes(source.read_bytes())
    assert sha(archive)==row['sha256']
for name in ['README.md','formalization.yaml']:
    (P/name).write_bytes((D/name).read_bytes())
    assert sha(P/name)==sha(D/name)

# Archive the exact preparer procedure and reviewable wrapper diffs, while
# avoiding a nested project or extra Solution.lean validation overlay.
source=E/'draft-source';source.mkdir()
rename={'README.md':'README.candidate.md','formalization.yaml':'formalization.candidate.yaml'}
for name in ['README.md','formalization.yaml','prepare_draft.py','install_candidate.py',
             'ARCHIVE-AND-INSTALL-PLAN.json','DRAFT-CHECKS.json','README.md.diff','formalization.yaml.diff']:
    (source/rename.get(name,name)).write_bytes((D/name).read_bytes())
failed=source/'initial-environment-attempt';failed.mkdir()
for path in sorted((D/'initial-environment-attempt').iterdir()):
    (failed/path.name).write_bytes(path.read_bytes())
assert not subprocess.check_output(['git','-C',str(W),'diff','--name-only'])
print(json.dumps({'installed':'two authorized wrappers; exact originals archived',
    'prepackaging_inputs':len(originals),'baseline_sha256':sha(E/'baseline.json'),
    'current_README_sha256':sha(P/'README.md'),'current_metadata_sha256':sha(P/'formalization.yaml'),
    'all_existing_manifests':manifests,'project':str(P)},indent=2))
