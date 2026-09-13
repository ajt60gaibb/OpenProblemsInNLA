"""Read-only exact MF-16 candidate input inventory and frozen-context check.
This script runs no Lean, Lake, cache, network, or Git mutation command.
"""
from pathlib import Path
import hashlib,json,os
E=Path(__file__).resolve().parent
P=E.parents[1]
W=P.parents[2]
OUTER=E/'EVIDENCE-MANIFEST.json'
EXCLUDED_DIRS={'.lake','.verification','__pycache__'}
EXCLUDED_SUFFIXES={'.olean','.ilean','.trace','.pyc'}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def eligible_files():
    found=[];observed=[]
    for parent,directories,files in os.walk(P):
        for name in directories:
            path=Path(parent)/name
            if name in EXCLUDED_DIRS:
                observed.append(str(path.relative_to(P))+'/')
            else:
                assert not path.is_symlink(),path
        directories[:]=sorted(d for d in directories if d not in EXCLUDED_DIRS)
        for name in sorted(files):
            path=Path(parent)/name
            if path==OUTER:
                continue
            if path.suffix in EXCLUDED_SUFFIXES:
                observed.append(str(path.relative_to(P)))
                continue
            assert path.is_file() and not path.is_symlink(),path
            assert path.resolve().is_relative_to(P),path
            found.append(path)
    return sorted(found),sorted(observed)

def verify():
    assert OUTER.is_file() and not OUTER.is_symlink()
    record=json.loads(OUTER.read_text())
    assert record['exact_self_exclusion']==str(OUTER.relative_to(P))
    assert set(record['generated_noninputs']['directories'])==EXCLUDED_DIRS
    assert set(record['generated_noninputs']['suffixes'])==EXCLUDED_SUFFIXES
    actual,observed=eligible_files()
    assert set(record['files'])=={os.path.relpath(path,E) for path in actual}
    assert record['file_count']==len(record['files'])
    assert record['total_including_this_outer_manifest']==len(record['files'])+1
    for name,item in record['files'].items():
        path=(E/name).resolve()
        assert path.is_relative_to(P),name
        assert sha(path)==item['sha256'] and path.stat().st_size==item['bytes'],name
    nested=sorted(n for n in record['files'] if Path(n).name==OUTER.name)
    assert record['nested_same_basename_manifests_included']==nested and len(nested)==5
    for key,path in [('handoff_sha256',E/'CANDIDATE-HANDOFF.md'),('integrity_sha256',E/'integrity.json'),
      ('proof_freeze_sha256',P/'verification/proof-freeze.json'),('statement_freeze_sha256',P/'reviews/statement-freeze.json')]:
        assert sha(path)==record[key],key
    baseline=json.loads((E/'baseline.json').read_text())
    integrity=json.loads((E/'integrity.json').read_text())
    assert sha(W/'problem_ids.json')==baseline['registry_sha256']
    for name,item in integrity['repository_static_inputs'].items():
        assert sha(W/name)==item['sha256'] and (W/name).stat().st_size==item['bytes'],name
    proof=json.loads((P/'verification/proof-freeze.json').read_text())
    statement=json.loads((P/'reviews/statement-freeze.json').read_text())
    assert len(proof['files'])==182 and len(statement['files'])==45
    for freeze in [proof,statement]:
        for name,h in freeze['files'].items():
            path=P/'verification/pre-candidate-README.md' if name=='README.md' else P/name
            assert sha(path)==h,name
    assert proof['source_files']==statement['source_files']
    assert len(proof['source_files'])==14
    for name,h in proof['source_files'].items():
        assert sha(W/name)==h,name
    assert sha(P/'README.md')==integrity['current_README_sha256']
    assert sha(P/'formalization.yaml')==integrity['current_formalization_yaml_sha256']
    return {'verdict':'PASS: exact complete project input inventory and all bound bytes; unchanged frozen original context',
      'bound_files':len(record['files']),'total_files':len(record['files'])+1,
      'included_nested_same_basename_manifests':len(nested),'manifest_sha256':sha(OUTER),
      'handoff_sha256':record['handoff_sha256'],'integrity_sha256':record['integrity_sha256'],
      'observed_generated_noninputs':observed,'Linux_Comparator_execution':'pending'}

if __name__=='__main__':
    print(json.dumps(verify(),indent=2))
