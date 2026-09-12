#!/usr/bin/env python3
"""Read-only integration identity check; evidence output is outside checkout."""
import collections
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import unicodedata

root = Path('/private/tmp/nla-pr141')
out = Path('/private/tmp/nla-review-trace/pr141-integration-review.json')
base = '24f4c834b4245fc9ce55003689a6db5e579be3d5'
target = 'randomized-and-low-rank-approximation/TR-01/README.md'
targetdir = str(Path(target).parent) + '/'
allowed = {
    'CATALOG.md', 'README.md', 'RESOLVED.md',
    'randomized-and-low-rank-approximation/README.md', target,
    targetdir + 'problem.tex', targetdir + 'problem.pdf',
}
def git(*args):
    return subprocess.check_output(['git', '-C', str(root), *args])
def blobhash(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
def sha256(data):
    return hashlib.sha256(data).hexdigest()
records = []
for item in git('ls-tree', '-rz', base).split(b'\0'):
    if not item:
        continue
    meta, name = item.split(b'\t', 1)
    mode, kind, oid = meta.decode().split()
    records.append((name.decode(), mode, kind, oid))
manifest = []
for name, mode, kind, oid in records:
    path = root / name
    exists = path.exists() or path.is_symlink()
    if exists:
        data = str(path.readlink()).encode() if path.is_symlink() else path.read_bytes()
        current = blobhash(data)
        curmode = '120000' if path.is_symlink() else ('100755' if path.stat().st_mode & 0o111 else '100644')
    else:
        data, current, curmode = b'', None, None
    manifest.append(dict(path=name, base_blob=oid, current_blob=current,
                         current_sha256=sha256(data) if exists else None,
                         byte_identical=kind == 'blob' and current == oid,
                         mode_identical=curmode == mode))
changed = [r['path'] for r in manifest if not r['byte_identical'] or not r['mode_identical']]
base_registry_raw = git('show', base + ':problem_ids.json')
current_registry_raw = (root / 'problem_ids.json').read_bytes()
registry = json.loads(base_registry_raw)
current_registry = json.loads(current_registry_raw)
canonical_dirs = [str(Path(path).parent) + '/' for key, path in registry.items() if key != 'TR-01']
canonical = [r for r in manifest if any(r['path'].startswith(prefix) for prefix in canonical_dirs)]
references = [r for r in manifest if r['path'].startswith('references/')]
tool_policy = [r for r in manifest if r['path'].startswith(('tools/', 'tests/', '.github/'))
               or r['path'] in {'AGENTS.md', 'problem_ids.json', 'CONTRIBUTING.md'}]
base_target = git('show', base + ':' + target).decode()
current_target = (root / target).read_text()
def section(text, heading):
    return re.search(r'^' + re.escape(heading) + r'\n.*?(?=^## |\Z)', text, re.M | re.S).group(0)
target_old = section(base_target, '## Problem statement')
target_new = section(current_target, '## Problem statement')
base_resolved = git('show', base + ':RESOLVED.md').decode()
current_resolved = (root / 'RESOLVED.md').read_text()
added_section = re.search(r'<a id="tr-01"></a>\n.*?(?=<a id="ie-01"></a>)', current_resolved, re.S)
removed = current_resolved[:added_section.start()] + current_resolved[added_section.end():] if added_section else None
explicit_anchors = re.findall(r'<a\s+(?:id|name)=["\']([^"\']+)', current_resolved)
headings = re.findall(r'^#{1,6}\s+(.+?)\s*$', current_resolved, re.M)
def heading_slug(heading):
    text = re.sub(r'<[^>]+>', '', heading).lower()
    return ''.join(c for c in text if c in '-_ ' or unicodedata.category(c)[0] in 'LNM').replace(' ', '-')
slugs = [heading_slug(h) for h in headings]
duplicates = lambda values: sorted(k for k,v in collections.Counter(values).items() if v > 1)
anchor_duplicates = duplicates(explicit_anchors)
heading_duplicates = duplicates(slugs)
anchor_collisions = sorted(set(explicit_anchors) & set(slugs))
index_checks = {}
for name in ['CATALOG.md', 'randomized-and-low-rank-approximation/README.md']:
    before = git('show', base + ':' + name).decode()
    after = (root / name).read_text()
    def rows(text):
        return [line for line in text.splitlines() if line.startswith('| [') and not re.search(r'\[TR-01\]', line)]
    index_checks[name] = dict(unrelated_rows_byte_identical=rows(before) == rows(after),
                             unrelated_row_count=len(rows(before)),
                             tr01_rows=len(re.findall(r'^\| \[TR-01\]', after, re.M)))
all_current = set(git('ls-files', '-z').decode().split('\0')) - {''}
all_current.update(set(git('ls-files', '--others', '--exclude-standard', '-z').decode().split('\0')) - {''})
added = sorted(all_current - {r['path'] for r in manifest})
unexpected_added = [name for name in added if not name.startswith('references/maintainer-review-2026-09-12-tr01/')]
unrelated_modified = sorted(set(changed) - allowed)
checks = {
    'base_registry_byte_identical': current_registry_raw == base_registry_raw,
    'all_id_path_pairs_unchanged': current_registry == registry,
    'all_published_paths_exist': all((root / path).is_file() for path in registry.values()),
    'all_published_readmes_keep_id_heading': all(re.match(r'#\s+' + re.escape(key) + r'\b', (root / path).read_text()) for key, path in registry.items()),
    'original_tr01_target_byte_identical': target_old == target_new,
    'tr01_original_references_byte_identical': section(base_target, '## References') == section(current_target, '## References'),
    'all_unrelated_base_files_byte_and_mode_identical': not unrelated_modified,
    'all_unrelated_canonical_files_byte_identical': all(r['byte_identical'] and r['mode_identical'] for r in canonical),
    'all_existing_reference_files_byte_identical': all(r['byte_identical'] and r['mode_identical'] for r in references),
    'all_policy_renderer_validator_test_files_byte_identical': all(r['byte_identical'] and r['mode_identical'] for r in tool_policy),
    'resolved_only_tr01_section_added': removed == base_resolved,
    'resolved_one_tr01_anchor': explicit_anchors.count('tr-01') == 1,
    'resolved_one_tr01_heading': len(re.findall(r'^### .*\bTR-01\b', current_resolved, re.M)) == 1,
    'resolved_no_duplicate_explicit_anchors': not anchor_duplicates,
    'resolved_no_duplicate_heading_slugs': not heading_duplicates,
    'resolved_no_explicit_heading_anchor_collisions': not anchor_collisions,
    'generated_indexes_preserve_unrelated_rows': all(row['unrelated_rows_byte_identical'] and row['tr01_rows'] == 1 for row in index_checks.values()),
    'only_tr01_audit_directory_added': not unexpected_added,
}
result = dict(
    timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    verdict='PASS' if all(checks.values()) else 'FAIL', base=base,
    head=git('rev-parse', 'HEAD').decode().strip(),
    scope='Current read-only working tree during integration; subsequent TR-01 evidence and PDF updates are not finalized here.',
    checks=checks, counts=dict(published_ids=len(registry), base_files=len(manifest),
        unchanged_base_files=sum(r['byte_identical'] and r['mode_identical'] for r in manifest),
        unrelated_canonical_files=len(canonical), existing_reference_files=len(references),
        policy_renderer_validator_test_files=len(tool_policy)),
    changed_base_paths=changed, unexpected_changed_base_paths=unrelated_modified,
    added_paths=added, unexpected_added_paths=unexpected_added,
    tr01_target_sha256=sha256(target_old.encode()), index_checks=index_checks,
    resolved=dict(added_section_sha256=sha256(added_section.group(0).encode()) if added_section else None,
        explicit_anchor_count=len(explicit_anchors), heading_count=len(headings),
        duplicate_explicit_anchors=anchor_duplicates, duplicate_heading_slugs=heading_duplicates,
        explicit_heading_collisions=anchor_collisions), manifest=manifest)
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({key:value for key,value in result.items() if key != 'manifest'}, indent=2))
