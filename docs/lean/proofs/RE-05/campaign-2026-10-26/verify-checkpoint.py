#!/usr/bin/env python3
"""Check an RE05 checkpoint's exact local or immutable-Git file hashes."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

B = Path(__file__).resolve().parent
R = B.parents[4]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--checkpoint', required=True, help='Checkpoint JSON filename in this directory')
p.add_argument('--git-ref', help='Read immutable Git blobs instead of working files')
a = p.parse_args()
assert Path(a.checkpoint).name == a.checkpoint and a.checkpoint.endswith('.json')

def read(path):
    assert not Path(path).is_absolute() and '..' not in Path(path).parts
    if a.git_ref:
        return subprocess.check_output(['git', 'show', a.git_ref + ':' + path], cwd=R)
    return (R / path).read_bytes()

j = json.loads(read(str((B / a.checkpoint).relative_to(R))))
for name, expected in {**j['file_sha256'], **j['TR04_canonical205_sha256']}.items():
    assert hashlib.sha256(read(name)).hexdigest() == expected, name
assert len(json.loads(read('problem_ids.json'))) == 217
assert j['complete_RE05_Target_proved'] is False
print(json.dumps({'passed': True, 'checkpoint': a.checkpoint,
                  'checkpoint_files': len(j['file_sha256']),
                  'TR04_preserved_inputs': 205, 'permanent_IDs': 217,
                  'git_ref': a.git_ref, 'complete_RE05_Target_proved': False}, indent=2))
