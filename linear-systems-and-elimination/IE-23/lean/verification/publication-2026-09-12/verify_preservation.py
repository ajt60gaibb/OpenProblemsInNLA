"""Hash-bound IE23 publication preservation and original-target audit."""
from pathlib import Path
from collections import Counter
import copy,datetime,hashlib,json,re,subprocess,yaml

P=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
W=P.parents[2]
baseline=json.loads((E/'baseline.json').read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
revision=baseline['candidate'];upstream=baseline['upstream_base']
wrappers={'README.md','formalization.yaml'}
preserved={}
for name,h in baseline['candidate_inputs'].items():
    raw=subprocess.check_output(['git','show',revision+':linear-systems-and-elimination/IE-23/lean/'+name],cwd=W)
    assert hashlib.sha256(raw).hexdigest()==h,name
    if name not in wrappers:
        assert sha(P/name)==h,name
        preserved[name]=h
assert len(preserved)==188
for name,archive in [('README.md','README.linux-candidate.md'),('formalization.yaml','formalization.linux-candidate.yaml')]:
    assert sha(E/'archive'/archive)==baseline['candidate_inputs'][name]

for folder,files in baseline['unchanged_evidence'].items():
    directory=P/'verification'/folder
    current={str(f.relative_to(directory)):sha(f) for f in directory.rglob('*') if f.is_file()}
    assert current==files,folder
    outer=json.loads((directory/'EVIDENCE-MANIFEST.json').read_text())
    assert set(outer['files'])==set(current)-{'EVIDENCE-MANIFEST.json'},folder
    assert len(outer['files'])==outer['file_count']
    for name,row in outer['files'].items():
        assert sha(directory/name)==row['sha256'] and (directory/name).stat().st_size==row['bytes'],name
assert len(baseline['unchanged_evidence']['linux-2026-09-12'])==331
assert len(baseline['unchanged_evidence']['root-operational-2026-09-12'])==7

freeze=json.loads((P/'reviews/proof-freeze.json').read_text())
for name,h in freeze['files'].items():
    expected=h['sha256']
    if name=='README.md': assert sha(P/'verification/linux-candidate-2026-09-12/README.statement.md')==expected
    else: assert sha(P/name)==expected,name
assert len(freeze['files'])==104

registry=json.loads((W/'problem_ids.json').read_text())
original_registry=json.loads(subprocess.check_output(['git','show',upstream+':problem_ids.json'],cwd=W))
assert registry==original_registry and len(registry)==217
counts=Counter()
for identifier,row in baseline['canonical_originals'].items():
    content=(W/row['path']).read_text()
    status=re.search(r'^\*\*Status:\*\* (.+)$',content,re.M).group(1).strip()
    counts[status]+=1
    if identifier!='IE-23': assert sha(W/row['path'])==row['sha256'],identifier
    else: assert status=='Lean verified'
for identifier in baseline['prior_Lean_verified']:
    assert '**Status:** Lean verified' in (W/registry[identifier]).read_text(),identifier
assert len(baseline['prior_Lean_verified'])==16
assert counts=={'Lean verified':17,'Solved':75,'Open':53,'Partially resolved':72},counts

old=(E/'archive/README.canonical-before.md').read_text()
new=(P.parent/'README.md').read_text()
assert old[old.index('## Problem statement\n'):]==new[new.index('## Problem statement\n'):]
assert new.count('## Lean proof and verification evidence - 2026-09-12')==1
oldresolved=(E/'archive/RESOLVED.before.md').read_text();newresolved=(W/'RESOLVED.md').read_text()
start='### IE-23 - Negative resolution\n';end='The related order-five rook bound'
assert oldresolved.split(start)[0]==newresolved.split(start)[0]
assert oldresolved[oldresolved.index(end):]==newresolved[newresolved.index(end):]

oldmeta=yaml.safe_load((E/'archive/formalization.linux-candidate.yaml').read_text())
newmeta=yaml.safe_load((P/'formalization.yaml').read_text())
paths=[('status','scope'),('review','status'),('review','notes'),('review','linux_verification','status'),('review','linux_verification','note')]
a=copy.deepcopy(oldmeta);b=copy.deepcopy(newmeta)
for path in paths:
    x=a;y=b
    for key in path[:-1]:x=x[key];y=y[key]
    assert x[path[-1]]!=y[path[-1]],path
    x.pop(path[-1]);y.pop(path[-1])
assert a==b
config=json.loads((P/'comparator.json').read_text())
assert [r['declaration'] for r in newmeta['status']['main_results']]==config['theorem_names']
assert len(config['theorem_names'])==8 and config['definition_names']==[]
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
assert newmeta['project']['affiliations']['George Stepaniants']=='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
for file in [P/'README.md',P/'formalization.yaml',P.parent/'README.md']:
    assert not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}',file.read_text()),file

allowed={'README.md','CATALOG.md','RESOLVED.md','linear-systems-and-elimination/README.md',
 'linear-systems-and-elimination/IE-23/README.md','linear-systems-and-elimination/IE-23/problem.tex',
 'linear-systems-and-elimination/IE-23/problem.pdf','linear-systems-and-elimination/IE-23/lean/README.md',
 'linear-systems-and-elimination/IE-23/lean/formalization.yaml'}
changed=set(subprocess.check_output(['git','diff','--name-only','HEAD'],cwd=W).decode().splitlines())
assert changed==allowed,changed
entries={}
for line in subprocess.check_output(['git','ls-tree','-rz',upstream],cwd=W).split(b'\0'):
    if not line: continue
    info,name=line.split(b'\t',1);mode,kind,oid=info.decode().split();name=name.decode()
    assert kind=='blob'
    if name not in allowed: entries[name]=oid
names=list(entries)
r=subprocess.run(['git','hash-object','--stdin-paths'],cwd=W,input=('\n'.join(names)+'\n').encode(),capture_output=True)
assert r.returncode==0,r.stderr
actual=r.stdout.decode().splitlines();assert len(actual)==len(names)
assert all(entries[name]==h for name,h in zip(names,actual))
(E/'preserved-upstream-files.json').write_text(json.dumps({'base':upstream,'file_count':len(entries),'files':entries},indent=2)+'\n')
diff=subprocess.run(['git','diff','--check','HEAD','--',*sorted(allowed)],cwd=W,capture_output=True)
(E/'scoped-diff-check.log').write_bytes(diff.stdout+diff.stderr);assert diff.returncode==0
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verdict':'PASS: publication identity and scope',
 'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=W).decode().strip(),
 'candidate':revision,'upstream_base':upstream,'verified_input_count':190,'unchanged_nonwrapper_inputs':188,
 'preserved_nonREADME_proof_inputs':103,'exact_prior_wrappers_archived':True,
 'Linux_evidence_files_unchanged':331,'root_acceptance_evidence_files_unchanged':7,
 'all_nested_manifests_unchanged':True,'permanent_IDs_preserved':217,'other_canonical_pages_unchanged':216,
 'prior_Lean_verified_entries_unchanged':baseline['prior_Lean_verified'],'canonical_original_target_bytes_unchanged':True,
 'RESOLVED_only_IE23_block_changed':True,'changed_manifest_fields':['.'.join(x) for x in paths],
 'exact_exports':config['theorem_names'],'remaining_manifest_structure_unchanged':True,
 'status_counts':dict(counts),'preserved_upstream_files':len(entries),
 'upstream_file_manifest_sha256':sha(E/'preserved-upstream-files.json'),
 'changed_tracked_files':sorted(changed),'publication_sha256':{n:sha(W/n) for n in sorted(changed)},
 'scoped_diff_check':'PASS; immutable original execution logs excluded',
 'new_Lean_build_or_Linux_execution':False,'publication_commit_or_push':False}
(E/'INTEGRITY-CHECKS.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['publication_sha256','exact_exports','prior_Lean_verified_entries_unchanged']},indent=2))
