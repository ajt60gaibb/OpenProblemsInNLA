#!/usr/bin/env python3
"""Read-only preservation check for the dated RA-12 9a697fd integration.

Run at its recorded integration commit, with both parent commits available.
This verifies source continuity, not a new mathematical theorem or CI approval.
"""
from pathlib import Path
import hashlib
from collections import Counter
import json
import os
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RECORD = HERE / 'main-integration-2026-09-12-9a697fd.json'


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])


def old(commit, path):
    return git('show', commit + ':' + path)


def fingerprint(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def blob(path, mode):
    p = ROOT / path
    return os.readlink(p).encode() if mode == b'120000' else p.read_bytes()


def main():
    record = json.loads(RECORD.read_text())
    prior, incoming = record['prior_head'], record['incoming_commit']
    reference = record['reference_readme']
    for path, expected in record['protected_submission_files'].items():
        assert fingerprint(old(prior, path)) == expected, path + ': prior hash'
        data = (ROOT / path).read_bytes()
        if path == reference:
            assert data.startswith(old(prior, path)), path + ': historical prefix'
        else:
            assert fingerprint(data) == expected, path + ': protected bytes'
    incoming_checked = 0
    incoming_exact = 0
    for entry in git('ls-tree', '-r', '-z', incoming).split(b'\0'):
        if not entry:
            continue
        meta, path_bytes = entry.split(b'\t', 1)
        mode, kind, expected = meta.split()
        assert kind == b'blob', path_bytes
        path = path_bytes.decode()
        data = blob(path, mode)
        if path == reference:
            assert data.startswith(old(incoming, path)), 'incoming reference prefix'
        else:
            actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest().encode()
            assert actual == expected, path + ': accepted incoming blob changed'
            incoming_exact += 1
        incoming_checked += 1
    assert incoming_checked == record['incoming_tracked_blobs_checked']
    assert incoming_exact == record['incoming_tracked_blobs_byte_identical']
    registry_bytes = (ROOT / 'problem_ids.json').read_bytes()
    assert registry_bytes == old(incoming, 'problem_ids.json')
    registry = json.loads(registry_bytes)
    previous = json.loads(old(prior, 'problem_ids.json'))
    assert len(registry) == record['permanent_ids']
    assert len(previous) == record['prior_permanent_ids']
    assert all(registry[k] == v for k, v in previous.items())
    assert sorted(set(registry) - set(previous)) == record['retained_upstream_appended_ids']
    for identifier, path in registry.items():
        assert (ROOT / path).read_bytes() == old(incoming, path), identifier
    counts = Counter()
    for identifier, path in registry.items():
        text = (ROOT / path).read_text()
        match = re.search(r'^\*\*Status:\*\* (.+?)\s*$', text, re.M)
        assert match, identifier + ': status'
        counts[match[1]] += 1
    assert dict(counts) == record['status_counts']
    assert '**Status:** Solved' in (ROOT / registry['RA-12']).read_text()
    assert '**Status:** Lean verified' in (ROOT / registry['IE-01']).read_text()
    for name in ['George Stepaniants', 'Department of Computing and Mathematical Sciences',
                 'California Institute of Technology']:
        assert name in (ROOT / registry['RA-12']).read_text()
        assert name in (ROOT / registry['RA-12']).with_name('solution.md').read_text()
    # Scope the privacy check to this submission, preserving unrelated incoming evidence.
    source_paths = list((HERE.parent).rglob('*')) + list((ROOT / registry['RA-12']).parent.iterdir())
    for path in source_paths:
        if path.is_file() and path.suffix in {'.md', '.json', '.py', '.tex', '.txt'}:
            assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',
                                 path.read_text()), str(path) + ': email address'
    for path, expected in record['current_files'].items():
        assert fingerprint((ROOT / path).read_bytes()) == expected, path + ': current hash'
    for path in [ROOT / reference, HERE / 'main-integration-2026-09-12-9a697fd.md']:
        for link in re.findall(r'\]\(([^)]+)\)', path.read_text()):
            target = link.split('#', 1)[0]
            if target and not re.match(r'[a-z]+:', target):
                assert (path.parent / target).exists(), (path, target)
    print('PASS:', len(record['protected_submission_files']), 'protected submission paths;',
          incoming_exact, 'accepted incoming blobs exact plus retained reference prefix;',
          len(registry), 'unchanged incoming canonical pages and IDs;',
          len(registry)-len(previous), 'upstream-appended IDs retained; all current hashes;',
          'accepted status distinctions and submission privacy PASS.')


if __name__ == '__main__':
    main()
