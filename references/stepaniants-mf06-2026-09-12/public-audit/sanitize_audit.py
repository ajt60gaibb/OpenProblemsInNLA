#!/usr/bin/env python3
"""Publish metadata for the MF-06 public audit, without retrieved bodies."""
from pathlib import Path
from hashlib import sha1, sha256
import argparse
import json
import re

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--raw', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
raw_bytes = a.raw.read_bytes()
r = json.loads(raw_bytes)
assert r['ids'] == ['MF-06']

dispositions = {
 'https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/110': 'Related accepted JSR/growth submission for MF-05, MF-07 and MF-12; explicitly excludes an MF-06 resolution.',
 'https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/109': 'MF-12 arbitrary growth-exponent construction; not a perturbation lower-Lipschitz claim.',
 'https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/108': 'MF-07 uniform polynomial trajectory bound; no MF-06 resolution.',
 'https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/107': 'MF-05 local two-family Holder estimate of exponent 1/d; explicitly leaves MF-06 unaffected.',
 'https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/84': 'Unrelated MI-28 determinant inequality; matched exterior-power language.',
 'https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/5': 'Unrelated KE-03 eigenvalue-query result; matched spectral-radius language.',
 'https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/110#issuecomment-5641298800': 'Merge request for MF-05, MF-07 and MF-12 only.',
 'https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/110#pullrequestreview-5184118506': 'Review of MF-05, MF-07 and MF-12; expressly does not infer MF-06.',
 'https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/85#pullrequestreview-5182448353': 'Unrelated MI-28 proof and provenance review; matched exterior-power language.',
}
blob_meta = {}
for git_sha, text in r['contents'].items():
    b = text.encode('utf-8')
    assert sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == git_sha
    blob_meta[git_sha] = {'bytes': len(b), 'sha256': sha256(b).hexdigest()}

canonical = {}
inventory = {}
for head, tree in r['trees'].items():
    for row in tree['selected_files']:
        key = (row['path'], row['sha'])
        entry = inventory.setdefault(key, {'path': row['path'], 'git_blob_sha': row['sha'],
                                          **blob_meta[row['sha']], 'observed_heads': []})
        entry['observed_heads'].append(head)
    row = tree['canonical_files']['MF-06']
    assert row is not None
    canonical[row['sha']] = {'path': row['path'], 'git_blob_sha': row['sha'],
                             **blob_meta[row['sha']], 'status': 'Partially resolved'}

matches = []
for row in r['discussion_matches']:
    assert row['url'] in dispositions
    body = (row.get('body') or '').encode('utf-8')
    matches.append({'repo': row['repo'], 'url': row['url'], 'title': row.get('title'),
                    'kind': row['kind'], 'retrieved_body_bytes': len(body),
                    'retrieved_body_sha256': sha256(body).hexdigest(),
                    'reviewer_disposition': dispositions[row['url']]})

record = {
 'checked_utc': r['checked_utc'],
 'target': 'MF-06: the complete pointwise exponent-one lower bound for arbitrary compact complex families',
 'verdict': 'No already-public full resolution found in the bounded scope checked; all canonical copies remain Partially resolved.',
 'requested_repository': r['requested_repository'], 'network_source': r['network_source'],
 'repositories': r['repositories'], 'repository_metadata': r['repository_metadata'],
 'counts': {'repositories': len(r['repositories']), 'branch_heads': len(r['branches']),
            'distinct_commit_heads': len(r['trees']), 'distinct_selected_text_blobs': len(r['contents']),
            'issues_prs_comments_read': r['issues_prs_comments_read'],
            'pr_review_endpoints_read': r['pr_review_endpoints_read'],
            'pr_review_bodies_read': r['pr_review_bodies_read'],
            'discussion_matches': len(matches), 'new_blob_reads': r['new_blob_reads']},
 'branches': r['branches'], 'canonical_versions': list(canonical.values()),
 'text_inventory': [inventory[k] for k in sorted(inventory)],
 'discussion_matches': matches,
 'raw_private_record': {'sha256': sha256(raw_bytes).hexdigest(), 'bytes': len(raw_bytes),
                        'handling': 'Retained privately; not redistributed in the publication package.'},
 'immutable_blob_cache_provenance': r['immutable_blob_cache_provenance'],
 'cache_validation': 'All reused and freshly retrieved UTF-8 blob contents verified against their immutable Git blob object SHA-1. Branches, forks, issues, comments and reviews were retrieved afresh.',
 'privacy': 'Contains metadata, hashes, status fields and reviewer-written dispositions only. No retrieved document or discussion body and no contact email is included.',
 'scope': r['scope'],
}
s = json.dumps(record, indent=2, ensure_ascii=False) + '\n'
assert not re.search(r'\b[A-Za-z0-9.!#$%&*+/=?^_`{|}~-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)+\b', s)
a.output.write_text(s)
print(json.dumps({'path': str(a.output), 'bytes': len(s.encode()), 'sha256': sha256(s.encode()).hexdigest(), 'counts': record['counts']}, indent=2))
