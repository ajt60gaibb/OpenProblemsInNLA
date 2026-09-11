"""Read-only check of the frozen seven-PR integration, independent of worktree."""
import subprocess, re, json, collections, difflib
from pathlib import Path

repo = '/private/tmp/nla-review-wave2-20260911'
base = 'ab754fabe3d48dc8d6eab6bcffce583e46d2b88f'
final = '85973354df42637636e2556c33169b5c4f247caf'
prs = [40, 47, 54, 62, 64, 78, 81]
shared = {'CATALOG.md', 'README.md', 'RESOLVED.md', 'references/README.md',
          'tools/render_problems.py', 'tools/render_reviewed_tex.py'}

def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo, text=True)

def read(ref, path):
    return git('show', ref + ':' + path)

def tree(ref):
    result = {}
    for line in git('ls-tree', '-r', ref).splitlines():
        spec, path = line.split('\t', 1)
        result[path] = tuple(spec.split())
    return result

bt, ft = tree(base), tree(final)
files, union, ptree = [], set(), {}
for n in prs:
    ref = f'origin/pr/{n}'
    pt = ptree[n] = tree(ref)
    changed = Path(f'/private/tmp/nla-review-wave2-artifacts/pr-{n}/REVIEW-CHANGED-FILES.txt').read_text().splitlines()
    union.update(changed)
    paths = set(changed) - shared
    files.append({'pr': n, 'head': git('rev-parse', ref).strip(),
                  'unique_count': len(paths),
                  'mismatches': [p for p in sorted(paths) if pt.get(p) != ft.get(p)]})

pattern = re.compile(r'^[^/]+/([A-Z]{2}-\d{2,})/README\.md$')
bpaths = {pattern.fullmatch(p)[1]: p for p in bt if pattern.fullmatch(p)}
fpaths = {pattern.fullmatch(p)[1]: p for p in ft if pattern.fullmatch(p)}
loss, counts = [], collections.Counter()
for identifier, path in fpaths.items():
    new = read(final, path)
    counts[re.search(r'^\*\*Status:\*\* (.*)$', new, re.M)[1].strip()] += 1
    if identifier not in bpaths:
        continue
    old = read(base, bpaths[identifier])
    if old.splitlines()[0] != new.splitlines()[0]:
        loss.append({'id': identifier, 'error': 'heading'})
    for tag, i, j, k, l in difflib.SequenceMatcher(a=old.splitlines(), b=new.splitlines(), autojunk=False).get_opcodes():
        if tag in ('delete', 'replace'):
            removed = [line for line in old.splitlines()[i:j]
                       if line.strip() and not line.startswith(('**Status:**', '**Last checked:**'))]
            if removed:
                loss.append({'id': identifier, 'removed': removed})

render = read(final, 'tools/render_problems.py')
render2 = read(final, 'tools/render_reviewed_tex.py')
scriptdiff = {}
for n in prs:
    if 'tools/render_reviewed_tex.py' not in ptree[n]:
        scriptdiff[str(n)] = {'source_absent': True}
        continue
    old = read(f'origin/pr/{n}', 'tools/render_reviewed_tex.py')
    scriptdiff[str(n)] = {'same': old == render2,
                         'removed_nonblank_lines': [line for line in old.splitlines()
                                                   if line.strip() and line not in render2.splitlines()]}

result = {
    'base': base, 'integration': final, 'files': files,
    'total_unique_contributions': sum(x['unique_count'] for x in files),
    'deleted_base_files': sorted(set(bt) - set(ft)),
    'changed_outside_contributions': [p for p in git('diff', '--name-only', base, final).splitlines() if p not in union],
    'original_id_count': len(bpaths), 'merged_id_count': len(fpaths),
    'id_paths_preserved': bpaths == fpaths,
    'canonical_original_losses': loss, 'statuses': dict(counts),
    'special_breaks': {identifier: render.count(f'if identifier == "{identifier}":') for identifier in ['SF-01', 'PF-05', 'RE-05', 'IE-20']},
    'manuscript_renderer_versions': scriptdiff,
    'IE10_status': re.search(r'^\*\*Status:\*\* (.*)$', read(final, 'eigenvalues-and-inverse-problems/IE-10/README.md'), re.M)[1],
    'IE10_resolved_mentions': [(i + 1, line) for i, line in enumerate(read(final, 'RESOLVED.md').splitlines()) if 'IE-10' in line],
}
Path(__file__).with_name('integration-85973354.json').write_text(json.dumps(result, indent=2))
print(json.dumps(result, indent=2))
