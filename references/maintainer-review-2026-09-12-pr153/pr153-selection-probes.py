#!/usr/bin/env python3
"""Independent scratch Git fixtures for the reviewed selector; no Lean executes."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

source = Path('/private/tmp/nla-pr153/tools/lean/projects.py')
records = []
def probe(name, mutation):
    with tempfile.TemporaryDirectory(prefix='nla-pr153-selection-', dir='/private/tmp') as td:
        root = Path(td)
        def git(*args):
            return subprocess.check_output(['git', '-C', td, *args], stderr=subprocess.STDOUT)
        git('init', '-q')
        registry = {'IE-19':'linear/IE-19/README.md', 'MI-19':'matrix/MI-19/README.md'}
        (root/'problem_ids.json').write_text(json.dumps(registry))
        for canonical in registry.values():
            readme = root/canonical
            readme.parent.mkdir(parents=True)
            readme.write_text('# '+readme.parent.name+'\n\n**Status:** Lean verified\n')
            project = readme.parent/'lean'
            project.mkdir()
            for file in ['Challenge.lean','Solution.lean','Δ.lean','two words.lean','formalization.yaml']:
                (project/file).write_text('-- fixture\n')
        git('add','.')
        git('-c','user.name=Independent reviewer','-c','user.email=audit@localhost','commit','-qm','base fixture')
        base=git('rev-parse','HEAD').decode().strip()
        mutation(root)
        git('add','-A')
        git('-c','user.name=Independent reviewer','-c','user.email=audit@localhost','commit','-qm',name)
        changed=git('diff','--name-only','--no-renames',base,'HEAD','--').decode().splitlines()
        raw_changed=git('diff','--name-only','--no-renames','-z',base,'HEAD','--').decode().rstrip('\0').split('\0')
        result=subprocess.run([sys.executable,str(source),'--root',td,'--base-ref',base],capture_output=True,text=True)
        matrix=json.loads(result.stdout) if result.returncode==0 else None
        records.append(dict(case=name,returncode=result.returncode,changed_output=changed,
                            changed_raw=raw_changed,matrix=matrix,stderr=result.stderr))

def modify(root, path):
    file=root/path
    file.parent.mkdir(parents=True,exist_ok=True)
    file.write_text('modified fixture\n')

probe('ordinary proof modification',lambda root:modify(root,'linear/IE-19/lean/Solution.lean'))
probe('Unicode dependency proof modification',lambda root:modify(root,'linear/IE-19/lean/Δ.lean'))
probe('space filename modification',lambda root:modify(root,'linear/IE-19/lean/two words.lean'))
probe('quoted filename modification',lambda root:modify(root,'linear/IE-19/lean/quoted"name.lean'))
probe('partial project deletion',lambda root:(root/'linear/IE-19/lean/Solution.lean').unlink())
probe('complete project deletion',lambda root:shutil.rmtree(root/'linear/IE-19/lean'))
probe('complete project rename',lambda root:(root/'linear/IE-19/lean').rename(root/'linear/IE-19/lean-archive'))
probe('shared schema modification',lambda root:modify(root,'docs/lean/schema/v0.4.schema.json'))
probe('shared toolchain modification',lambda root:modify(root,'docs/lean/ci-toolchain/lean-toolchain'))
probe('shared tool modification',lambda root:modify(root,'tools/lean/harness.py'))
probe('source-only registered project addition',lambda root: (
    (root/'problem_ids.json').write_text(json.dumps({**json.loads((root/'problem_ids.json').read_text()),'MI-20':'matrix/MI-20/README.md'})),
    modify(root,'matrix/MI-20/lean/Draft.lean')))
result=dict(reviewed_head='eaf3b80698555171804bef29e3a9e2b1607bc875',
            selector_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),cases=records)
Path('/private/tmp/nla-review-trace/pr153-selection-probes.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
