"""Read-only public fork/branch/discussion check for IE-04.

Requires authenticated GitHub CLI and writes a raw snapshot only at --output.
The published snapshot is separately sanitized to target-specific evidence.
No issue, comment, branch, or pull request is created or changed.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from datetime import datetime, timezone
import argparse
import os
import shutil
import base64
import hashlib
import json
import re
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--cache', type=Path, action='append', default=[], help='Optional prior raw audit snapshot; Git blob hashes are verified.')
args = parser.parse_args()
GH = os.environ.get('GH') or shutil.which('gh')
if not GH:
    raise SystemExit('Install GitHub CLI or set GH to its executable path.')
ROOT = 'ajt60gaibb/OpenProblemsInNLA'
IDS = ['IE-04']
REG = json.loads((Path(__file__).resolve().parents[3] / 'problem_ids.json').read_text())
OUT = args.output
PAT = re.compile(r'\bIE-04\b|smoothed|exponential.{0,60}(GEPP|pivot|elimination)|Gaussian.{0,60}(growth|tail)', re.I | re.S)


def api(endpoint, paged=False):
    cmd = [GH, 'api', endpoint]
    if paged:
        cmd += ['--paginate', '--slurp']
    for attempt in range(3):
        try:
            data = json.loads(subprocess.check_output(cmd, text=True, timeout=30))
            break
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
            if attempt == 2:
                raise
            time.sleep(attempt + 1)
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
                 or re.search('smooth|gauss|growth|tail|pivot', p, re.I))]
    return b['sha'], {'repo': b['repo'], 'canonical_files': {pid: paths.get(REG[pid]) for pid in IDS},
                      'selected_files': selected}


with ThreadPoolExecutor(max_workers=5) as pool:
    trees = dict(pool.map(get_tree, heads.values()))
blobs = {}
for tree in trees.values():
    for v in tree['selected_files']:
        blobs.setdefault(v['sha'], (tree['repo'], v['sha']))


CACHED_CONTENTS = {}
for cache in args.cache:
    CACHED_CONTENTS.update(json.loads(Path(cache).read_text())['contents'])
for blob_sha, content in CACHED_CONTENTS.items():
    data = content.encode()
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob_sha

def read_blob(item):
    repo, sha = item
    if sha in CACHED_CONTENTS:
        return sha, CACHED_CONTENTS[sha]
    v = api('repos/' + repo + '/git/blobs/' + sha)
    return sha, base64.b64decode(v['content']).decode()


with ThreadPoolExecutor(max_workers=5) as pool:
    contents = dict(pool.map(read_blob, blobs.values()))
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
    return matches, [(repo, p['number']) for p in prs]


with ThreadPoolExecutor(max_workers=5) as pool:
    batches = list(pool.map(discussion_for, sorted(repos)))
matches = [x for m, prs in batches for x in m]
prs = [x for m, prs in batches for x in prs]


def review_for(pair):
    repo, num = pair
    rows = api('repos/' + repo + '/pulls/' + str(num) + '/reviews?per_page=100', True)
    return len(rows), [{'repo': repo, 'pr': num, 'url': r['html_url'], 'body': r['body'],
                        'kind': 'PR review'} for r in rows if PAT.search(r.get('body') or '')]


with ThreadPoolExecutor(max_workers=5) as pool:
    reviews = list(pool.map(review_for, prs))
matches += [r for count, rs in reviews for r in rs]
record = {'checked_utc': datetime.now(timezone.utc).isoformat(), 'ids': IDS,
          'requested_repository': ROOT, 'network_source': source, 'repositories': sorted(repos),
          'branches': branches, 'trees': trees, 'contents': contents, 'discussion_matches': matches,
          'pr_review_bodies_read': sum(n for n, rs in reviews),
          'pr_review_endpoints_read': len(prs),
          'scope': 'All recursively returned public forks, every public branch head; canonical pages, root indexes, ID-named and smoothed/Gaussian/growth/tail/pivot-named text documents; matching issues, PR bodies and comments, plus all PR review bodies. Private/deleted/unpublished/unidentifiably named work is outside this bounded check.'}
OUT.write_text(json.dumps(record, indent=2) + '\n')
print(record['checked_utc'], len(repos), 'repos;', len(branches), 'heads;', len(contents), 'text files;', record['pr_review_bodies_read'], 'PR review bodies')
print('Statuses:', {pid: sorted({b['statuses'][pid] for b in branches}) for pid in IDS})
print('Discussion matches:', [(v['url'], v.get('title')) for v in matches])
print('Snapshot sha256:', hashlib.sha256(OUT.read_bytes()).hexdigest())
