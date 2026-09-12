"""Remove retrieved content and personal contact data from a private public-network snapshot."""
from pathlib import Path
import argparse, hashlib, json, re
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
d = json.loads(args.input.read_text())
paths = {}
for commit, tree in d['trees'].items():
    for item in tree['selected_files']:
        paths.setdefault(item['sha'], set()).add(item['path'])
records = []
for blob, content in sorted(d['contents'].items()):
    records.append({'git_blob_sha': blob, 'sha256': hashlib.sha256(content.encode()).hexdigest(), 'bytes': len(content.encode()), 'paths': sorted(paths.get(blob, [])), 'mentions_target_or_primary_id': bool(re.search(r'KE-05|2507[.]10144', content, re.I))})
heads = []
for head in d['branches']:
    row = dict(head)
    row['canonical_files'] = {pid: None if item is None else {'path': item['path'], 'git_blob_sha': item['sha']} for pid,item in d['trees'][head['sha']]['canonical_files'].items()}
    heads.append(row)
sanitized = {
    'checked_utc': d['checked_utc'], 'ids': d['ids'], 'requested_repository': d['requested_repository'], 'network_source': d['network_source'],
    'repositories': d['repositories'], 'repository_metadata': d['repository_metadata'], 'branches': heads,
    'counts': {'repositories':len(d['repositories']), 'branch_heads':len(heads), 'distinct_commit_trees':len(d['trees']), 'selected_text_blobs':len(records), 'issue_pr_and_comment_bodies':d['issues_prs_comments_read'], 'pr_review_endpoints':d['pr_review_endpoints_read'], 'pr_review_bodies':d['pr_review_bodies_read'], 'matching_discussion_bodies':len(d['discussion_matches'])},
    'document_fingerprints': records,
    'discussion_matches': [{'repo':x['repo'], 'url':x['url'], 'kind':x['kind'], 'body_sha256':hashlib.sha256((x.get('body') or '').encode()).hexdigest()} for x in d['discussion_matches']],
    'raw_private_snapshot_sha256': hashlib.sha256(args.input.read_bytes()).hexdigest(),
    'scope': d['scope'],
    'sanitization': 'Retrieved file contents, discussion bodies, identities, and personal contact information are omitted. Public repository/branch names, commit and blob identifiers, file paths, byte counts and digests are retained. The raw retrieval snapshot remains private.',
    'conclusion': 'No prior KE-05 resolution or mathematical objection was found within the stated public snapshot. All 47 canonical pages show Open and share one README blob. This is a bounded eligibility check, not a proof of global novelty.'
}
text=json.dumps(sanitized, indent=2)+'\n'
assert not re.search(r'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}',text)
args.output.write_text(text)
print('Sanitized snapshot:',hashlib.sha256(args.output.read_bytes()).hexdigest())
