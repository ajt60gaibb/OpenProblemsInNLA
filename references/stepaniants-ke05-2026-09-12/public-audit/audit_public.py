"""Read-only public fork/branch/discussion check for KE-05."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from datetime import datetime, timezone
import base64
import hashlib
import json
import re
import subprocess
import argparse
import os
import shutil

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--cache-snapshot', type=Path, action='append', default=[], help='Optional earlier full JSON snapshots; immutable Git blob text is reused by SHA only.')
args = parser.parse_args()
GH = os.environ.get('GH') or shutil.which('gh')
if not GH:
    raise SystemExit('Set GH to the GitHub CLI executable.')
ROOT = 'ajt60gaibb/OpenProblemsInNLA'
IDS = ['KE-05']
REG = {'KE-05': 'randomized-and-low-rank-approximation/KE-05/README.md'}
OUT = args.output
PAT = re.compile(r'\bKE-05\b|2507[.]10144|Shao.{0,60}(Lanczos|cluster|interpol)|cluster.{0,60}robust|small[-_ ]?block.{0,40}Lanczos|chi.{0,30}(mono|coef)|spectral.{0,30}gap.{0,50}interpol', re.I | re.S)


def api(endpoint, paged=False):
    cmd = [GH, 'api', endpoint]
    if paged:
        cmd += ['--paginate', '--slurp']
    data = json.loads(subprocess.check_output(cmd, text=True))
    return [item for page in data for item in page] if paged else data


metadata = api('repos/' + ROOT)
source = metadata.get('source', {}).get('full_name', ROOT)
repos = {ROOT, source}
queue = list(repos)
while queue:
    for item in api('repos/' + queue.pop() + '/forks?per_page=100', True):
        if item['full_name'] not in repos:
            repos.add(item['full_name'])
            queue.append(item['full_name'])


def branches_for(repo):
    return [{'repo': repo, 'branch': b['name'], 'sha': b['commit']['sha']}
            for b in api('repos/' + repo + '/branches?per_page=100', True)]


with ThreadPoolExecutor(max_workers=5) as pool:
    branches = [b for batch in pool.map(branches_for, sorted(repos)) for b in batch]
heads = {b['sha']: b for b in branches}


def get_tree(b):
    tree = api('repos/' + b['repo'] + '/git/trees/' + b['sha'] + '?recursive=1')
    assert not tree.get('truncated')
    paths = {v['path']: v for v in tree['tree'] if v['type'] == 'blob'}
    selected = [v for p, v in paths.items()
                if p.endswith(('.md', '.tex', '.py', '.txt')) and
                (any(pid in p for pid in IDS) or p in ['README.md', 'RESOLVED.md', 'CATALOG.md']
                 or re.search(r'small.?block|lanczos|cluster|interpola|shao|KE-05', p, re.I))]
    return b['sha'], {'repo': b['repo'], 'canonical_files': {pid: paths.get(REG[pid]) for pid in IDS},
                      'selected_files': selected}


with ThreadPoolExecutor(max_workers=5) as pool:
    trees = dict(pool.map(get_tree, heads.values()))
blobs = {}
for tree in trees.values():
    for v in tree['selected_files']:
        blobs.setdefault(v['sha'], (tree['repo'], v['sha']))


def read_blob(item):
    repo, sha = item
    v = api('repos/' + repo + '/git/blobs/' + sha)
    return sha, base64.b64decode(v['content']).decode()


cache = {}
cache_provenance = []
for cache_path in args.cache_snapshot:
    data = json.loads(cache_path.read_text())
    cache.update(data['contents'])
    cache_provenance.append({'snapshot_sha256': hashlib.sha256(cache_path.read_bytes()).hexdigest(), 'checked_utc': data['checked_utc'], 'contents_count': len(data['contents'])})
contents = {sha: cache[sha] for sha in blobs if sha in cache}
missing = [item for sha, item in blobs.items() if sha not in cache]
with ThreadPoolExecutor(max_workers=5) as pool:
    contents.update(dict(pool.map(read_blob, missing)))
for b in branches:
    b['statuses'] = {}
    for pid in IDS:
        v = trees[b['sha']]['canonical_files'][pid]
        b['statuses'][pid] = next((line for line in contents[v['sha']].splitlines()
                                   if '**Status:**' in line), 'Missing status') if v else 'Missing page'


def discussion_for(repo):
    entries = api('repos/' + repo + '/issues?state=all&per_page=100', True)
    prs = [x for x in entries if 'pull_request' in x]
    entries += api('repos/' + repo + '/issues/comments?per_page=100', True)
    entries += api('repos/' + repo + '/pulls/comments?per_page=100', True)
    matches = [{'repo': repo, 'url': x['html_url'], 'title': x.get('title'),
                'body': x.get('body'), 'kind': 'issue/PR/comment'} for x in entries
               if PAT.search((x.get('title') or '') + '\n' + (x.get('body') or ''))]
    return matches, [(repo, p['number']) for p in prs], len(entries)


with ThreadPoolExecutor(max_workers=5) as pool:
    batches = list(pool.map(discussion_for, sorted(repos)))
matches = [x for m, prs, count in batches for x in m]
prs = [x for m, prs, count in batches for x in prs]


def review_for(pair):
    repo, num = pair
    rows = api('repos/' + repo + '/pulls/' + str(num) + '/reviews?per_page=100', True)
    return len(rows), [{'repo': repo, 'pr': num, 'url': r['html_url'], 'body': r['body'],
                        'kind': 'PR review'} for r in rows if PAT.search(r.get('body') or '')]


with ThreadPoolExecutor(max_workers=5) as pool:
    reviews = list(pool.map(review_for, prs))
matches += [r for count, rs in reviews for r in rs]
repo_metadata = {}
for repo in sorted(repos):
    entry = api('repos/' + repo)
    repo_metadata[repo] = {k: entry.get(k) for k in ['full_name', 'private', 'default_branch', 'fork', 'forks_count', 'has_discussions']}
record = {'repository_metadata': repo_metadata, 'checked_utc': datetime.now(timezone.utc).isoformat(), 'ids': IDS,
          'requested_repository': ROOT, 'network_source': source, 'repositories': sorted(repos),
          'branches': branches, 'trees': trees, 'contents': contents, 'discussion_matches': matches,
          'pr_review_bodies_read': sum(n for n, rs in reviews),
          'issues_prs_comments_read': sum(count for m, prs, count in batches), 'pr_review_endpoints_read': len(prs), 'immutable_blob_cache_provenance': cache_provenance, 'new_blob_reads': len(missing),
          'scope': 'All recursively returned public forks, every public branch head; canonical pages, root indexes, KE-05-named, small-block/Lanczos/cluster/interpolation/Shao-named text documents; matching issues, PR bodies and comments, plus all PR review bodies. Private/deleted/unpublished/unidentifiably named work is outside this bounded check.'}
OUT.write_text(json.dumps(record, indent=2) + '\n')
print(record['checked_utc'], len(repos), 'repos;', len(branches), 'heads;', len(contents), 'text files;', record['pr_review_bodies_read'], 'PR review bodies')
print('Statuses:', {pid: sorted({b['statuses'][pid] for b in branches}) for pid in IDS})
print('Discussion matches:', [(v['url'], v.get('title')) for v in matches])
print('Snapshot sha256:', hashlib.sha256(OUT.read_bytes()).hexdigest())
