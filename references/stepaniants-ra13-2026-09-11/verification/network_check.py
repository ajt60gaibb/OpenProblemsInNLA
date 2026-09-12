from pathlib import Path
import argparse, base64, concurrent.futures, datetime, json, os, re, shutil, subprocess

GH = os.environ.get('GH', shutil.which('gh'))
if not GH:
    raise SystemExit('Install and authenticate the GitHub CLI, or set GH to its path.')
REQUESTED_ROOT = 'ajt60gaibb/OpenProblemsInNLA'
ID = 'RA-13'
parser = argparse.ArgumentParser(description='Read-only public RA-13 branch and discussion audit')
parser.add_argument('--output', type=Path, required=True)
OUT = parser.parse_args().output
registry = json.loads((Path(__file__).resolve().parents[3] / 'problem_ids.json').read_text())

def api(endpoint, paged=False):
    args = [GH, 'api', endpoint] + (['--paginate', '--slurp'] if paged else [])
    data = json.loads(subprocess.check_output(args, text=True))
    return [item for page in data for item in page] if paged else data

metadata = api(f'repos/{REQUESTED_ROOT}')
root = metadata.get('source', {}).get('full_name', REQUESTED_ROOT)
repos, todo = {root, REQUESTED_ROOT}, list({root, REQUESTED_ROOT})
while todo:
    for repo in api(f'repos/{todo.pop()}/forks?per_page=100', True):
        if repo['full_name'] not in repos:
            repos.add(repo['full_name'])
            todo.append(repo['full_name'])
branches = []
for repo in sorted(repos):
    for branch in api(f'repos/{repo}/branches?per_page=100', True):
        branches.append({'repo': repo, 'branch': branch['name'], 'sha': branch['commit']['sha']})
heads = {branch['sha']: branch for branch in branches}
id_pattern = re.compile(r'(?<![A-Za-z0-9])RA-13(?![A-Za-z0-9])', re.I)
scope_pattern = re.compile(r'\bRA-13\b|Gamma|trace.{0,30}tail|Hallman|absolute.{0,30}trace', re.I | re.S)

def get_tree(branch):
    data = api(f"repos/{branch['repo']}/git/trees/{branch['sha']}?recursive=1")
    assert not data.get('truncated'), 'Tree must be complete'
    paths = {item['path']: item for item in data['tree'] if item['type'] == 'blob'}
    selected = [item for path, item in paths.items() if
                (id_pattern.search(path) or path in ('README.md', 'RESOLVED.md', 'CATALOG.md') or
                 re.search(r'gamma|trace|hallman|ra13', path, re.I)) and
                path.endswith(('.md', '.tex', '.py', '.txt'))]
    return branch['sha'], {'repo': branch['repo'], 'canonical_file': paths.get(registry[ID]), 'selected_files': selected}

with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
    trees = dict(pool.map(get_tree, heads.values()))
blobs = {}
for tree in trees.values():
    for item in tree['selected_files']:
        blobs.setdefault(item['sha'], (tree['repo'], item['sha']))

def get_blob(item):
    repo, sha = item
    data = api(f'repos/{repo}/git/blobs/{sha}')
    return sha, base64.b64decode(data['content']).decode()

with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
    contents = dict(pool.map(get_blob, blobs.values()))
for branch in branches:
    item = trees[branch['sha']]['canonical_file']
    branch['status'] = next((line for line in contents[item['sha']].splitlines() if '**Status:**' in line), 'Missing status') if item else 'Missing page'

def get_discussions(repo):
    entries = api(f'repos/{repo}/issues?state=all&per_page=100', True)
    entries += api(f'repos/{repo}/issues/comments?per_page=100', True)
    entries += api(f'repos/{repo}/pulls/comments?per_page=100', True)
    return [{'repo': repo, 'url': item['html_url'], 'title': item.get('title'),
             'body': item.get('body'), 'state': item.get('state')}
            for item in entries if scope_pattern.search((item.get('title') or '') + '\n' + (item.get('body') or ''))]

with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
    matches = [item for result in pool.map(get_discussions, sorted(repos)) for item in result]
report = {
    'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'requested_repository': REQUESTED_ROOT, 'network_source_repository': root, 'id': ID,
    'scope': 'All public forks recursively returned from the network source, every public branch head, canonical RA-13 pages, ID-named and Gamma/trace/Hallman/ra13-named text documents, root README/RESOLVED/CATALOG files; matching issues, PR bodies, issue comments and PR inline-review comments in every repository. Private, deleted, unpublished and unidentifiably named work is outside this check.',
    'repositories': sorted(repos), 'branches': branches, 'trees': trees,
    'contents': contents, 'discussion_matches': matches,
}
OUT.parent.mkdir(parents=True, exist_ok=True)
report['contact_redaction'] = 'Public contact-address strings in text fields are redacted; mathematical and status content is unchanged.'
encoded = json.dumps(report, indent=2)
encoded = re.sub(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', '[public contact address redacted]', encoded)
OUT.write_text(encoded + '\n')
print(report['checked_utc'], len(repos), 'repositories', len(branches), 'branch heads', len(contents), 'distinct text documents')
print('Network source:', root)
print('Statuses:', sorted({branch['status'] for branch in branches}))
print('Discussion matches:', [(item['url'], item['title']) for item in matches])
