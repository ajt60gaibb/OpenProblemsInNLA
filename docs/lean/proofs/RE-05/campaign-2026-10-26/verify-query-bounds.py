#!/usr/bin/env python3
"""Verify the accepted deterministic RE05 query-bound checkpoint."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

B = Path(__file__).resolve().parent
R = B.parents[4]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--git-ref', help='Read immutable Git blobs instead of working files')
a = p.parse_args()

def read(path):
    if a.git_ref:
        return subprocess.check_output(['git', 'show', a.git_ref + ':' + path], cwd=R)
    return (R / path).read_bytes()

path = str((B / 'ACCEPTED_QUERY_BOUNDS_CHECKPOINT.json').relative_to(R))
j = json.loads(read(path))
for name, expected in {**j['file_sha256'], **j['TR04_canonical205_sha256']}.items():
    assert hashlib.sha256(read(name)).hexdigest() == expected, name
assert len(json.loads(read('problem_ids.json'))) == 217
assert j['complete_RE05_Target_proved'] is False
assert j['fixed_query_constants'] == {'C': 1000000, 'a': 1, 'b': 1}
print(json.dumps({'passed': True, 'checkpoint_files': len(j['file_sha256']),
                  'TR04_preserved_inputs': 205, 'permanent_IDs': 217,
                  'git_ref': a.git_ref, 'complete_RE05_Target_proved': False}, indent=2))
