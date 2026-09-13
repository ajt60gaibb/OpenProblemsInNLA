"""Seal the full actual RA-08 Linux-candidate input set.

Adapted from IS-03 candidate packaging. Includes every nested manifest and
excludes only this exact outer manifest among source/document/evidence inputs.
No proof, dependency, network or Git mutation command is executed.
"""
from pathlib import Path
import datetime, hashlib, json, os, subprocess

E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
outer=E/'EVIDENCE-MANIFEST.json'
excluded_dirs={'.lake','.verification','__pycache__'}
excluded_suffixes={'.olean','.ilean','.trace','.pyc'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not outer.exists(),'An existing sealed inventory must not be overwritten.'
def eligible():
    files=[]
    for parent,dirs,names in os.walk(P):
        dirs[:]=sorted(d for d in dirs if d not in excluded_dirs)
        for name in sorted(names):
            path=Path(parent)/name
            if path.resolve()==outer.resolve() or path.suffix in excluded_suffixes:continue
            assert path.is_file() and not path.is_symlink(),path
            files.append(path)
    return sorted(files)
baseline=json.loads((E/'baseline.json').read_text())
integrity=json.loads((E/'integrity.json').read_text())
assert integrity['verdict'].startswith('PASS installed')
archives={x['source']:P/x['archive'] for x in baseline['archive_plan']['archives_required_before_any_live_replacement']}
for n,row in baseline['original_project_inputs'].items():
    p=archives.get(n,P/n)
    assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],n
for n,h in integrity['current_wrappers'].items():assert sha(P/n)==h
assert not subprocess.check_output(['git','diff','--name-only'],cwd=W)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=W)
files={os.path.relpath(p,E):{'sha256':sha(p),'bytes':p.stat().st_size} for p in eligible()}
nested=sorted(n for n in files if Path(n).name==outer.name)
assert len(nested)==6
record={
    'phase':'RA-08 reviewed Linux candidate; full actual project input inventory',
    'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'worktree':str(W),'project':str(P),'base':baseline['base'],
    'canonical_status':'Solved, unchanged; actual Linux verification pending',
    'preparer':'/root/leancert_examples, prior independent final referee 1 now in a separate documentation role; no extra mathematical approval',
    'path_base':'Directory containing this outer manifest',
    'inventory_scope':'Every actual project source, document and evidence input, including all nested manifests',
    'exact_self_exclusion':str(outer.relative_to(P)),
    'generated_noninputs':{'directories':sorted(excluded_dirs),'suffixes':sorted(excluded_suffixes)},
    'file_count':len(files),'total_including_this_outer_manifest':len(files)+1,
    'nested_same_basename_manifests_included':nested,
    'original_project_input_count':len(baseline['original_project_inputs']),
    'wrapper_mutation_scope':['README.md refreshed with exact old archive','formalization.yaml refreshed with exact old archive'],
    'proof_freeze_sha256':sha(P/'verification/proof-freeze.json'),
    'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),
    'handoff_sha256':sha(E/'CANDIDATE-HANDOFF.md'),'integrity_sha256':sha(E/'integrity.json'),
    'files':files,
}
outer.write_text(json.dumps(record,indent=2)+'\n')
assert set(files)=={os.path.relpath(p,E) for p in eligible()}
for n,row in files.items():
    path=(E/n).resolve()
    assert path.is_relative_to(P.resolve())
    assert sha(path)==row['sha256'] and path.stat().st_size==row['bytes'],n
print(json.dumps({'verdict':'PASS exact complete candidate inventory',
    'bound_files':len(files),'total_files':len(files)+1,'nested_manifests':len(nested),
    'manifest_sha256':sha(outer),'handoff_sha256':record['handoff_sha256'],
    'integrity_sha256':record['integrity_sha256']},indent=2))
