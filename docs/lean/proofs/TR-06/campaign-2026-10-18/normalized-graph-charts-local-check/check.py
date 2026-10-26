#!/usr/bin/env python3
"""Snapshot and freshly replay the authored TR06 model bridge import closure.

Uses only pinned dependency objects, never project-local objects. This is an
author compilation receipt, not an independent mathematical source review.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess

ap = argparse.ArgumentParser()
ap.add_argument('--repo-root', type=Path, required=True)
ap.add_argument('--lean-bin', type=Path, required=True)
ap.add_argument('--dependency-root', type=Path, required=True)
ap.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
args = ap.parse_args()
project = args.repo_root.resolve() / 'lean-statements'
dest = args.output.resolve()
source = dest / 'source' / 'lean-statements'
objects = dest / 'fresh-build' / 'lib' / 'lean'
logs = dest / 'logs'
for p in (source, objects, logs):
    p.mkdir(parents=True, exist_ok=True)
if any(objects.rglob('*.olean')):
    raise SystemExit('Refusing to reuse earlier local objects; choose a new --output directory.')

sha = lambda b: hashlib.sha256(b).hexdigest()
targets = ['NLA.Proofs.TR06.NormalizedGraphCharts']
modules = []
seen = set()
entries = []
def visit(module):
    if module in seen:
        return
    seen.add(module)
    rel = Path(module.replace('.', '/')).with_suffix('.lean')
    path = project / rel
    if not path.exists():
        return
    data = path.read_bytes()
    for imported in re.findall(rb'^import\s+([\w.]+)', data, re.M):
        visit(imported.decode())
    out = source / rel
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(data)
    out.chmod(0o444)
    entries.append({'module': module, 'path': str(rel), 'sha256': sha(data),
                    'authored_model_module': module.startswith('NLA.Proofs.TR06.Model'), 'authored_graph_chart_module': module.startswith('NLA.Proofs.TR06.NormalizedGraphCharts')})
    modules.append((module, rel))
for target in targets:
    visit(target)
dependency_paths = [p / '.lake/build/lib/lean' for p in args.dependency_root.resolve().iterdir()
                    if (p / '.lake/build/lib/lean').is_dir()]
env = dict(os.environ, LEAN_PATH=':'.join(str(p) for p in [objects, *dependency_paths]))
consumer = '''import NLA.Proofs.TR06.NormalizedGraphCharts
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open NLA.TR06 NLA.Proofs.TR06
#assert_trust kernel NormalizedGraphCharts.rankOneTangent_radial
#assert_trust kernel NormalizedGraphCharts.chart_summands_linearIndependent
#assert_trust kernel NormalizedGraphCharts.exists_open_separating_neighborhood
#assert_trust kernel NormalizedGraphCharts.exists_normalizedGraph_chart
example {d : ℕ} {n : Fin d → ℕ} {r : ℕ} (hd : 0 < d) :
    ∀ z : normalizedAnnularGraph d n r,
      ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (expectedDimension d n r)))
          (normalizedAnnularGraph d n r),
        z ∈ e.target ∧ ContDiffOn ℝ 1 (fun v => (e v).val) e.source ∧
          ∀ v ∈ e.source, Function.Injective (fderiv ℝ (fun w => (e w).val) v) := by
  intro z
  obtain ⟨e,u,hu,heq,hsm,_hproj,hfull,_hformula⟩ :=
    NormalizedGraphCharts.exists_normalizedGraph_chart hd z
  exact ⟨e,heq ▸ e.map_source hu,hsm.of_le (by simp),hfull⟩
#print axioms NormalizedGraphCharts.exists_normalizedGraph_chart
'''
(source / 'ModelConsumer.lean').write_text(consumer)
(source / 'ModelConsumer.lean').chmod(0o444)
modules.append(('ModelConsumer', Path('ModelConsumer.lean')))
receipt = {'status': 'running', 'scope': 'author fresh source replay; no independent approval',
           'root_targets': targets, 'source_manifest': entries,
           'project_objects_reused': False, 'dependency_objects_reused': True,
           'dependency_library_paths': [str(p) for p in dependency_paths], 'checks': []}
receipt['lean_version'] = subprocess.check_output([str(args.lean_bin), '--version'], text=True).strip()
(dest / 'source-manifest.json').write_text(json.dumps(entries, indent=2) + '\n')
for module, rel in modules:
    out = objects / rel.with_suffix('.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    command = [str(args.lean_bin), '-o', str(out), str(rel)]
    result = subprocess.run(command, cwd=source, env=env, text=True, capture_output=True)
    log = logs / (module + '.log')
    log.write_text(result.stdout + result.stderr)
    receipt['checks'].append({'module': module, 'command': command,
        'source_sha256': sha((source / rel).read_bytes()), 'exit_code': result.returncode,
        'log': str(log.relative_to(dest)), 'log_sha256': sha(log.read_bytes()),
        'object_sha256': sha(out.read_bytes()) if out.exists() else None})
    print(module, result.returncode, flush=True)
    if result.returncode:
        receipt['status'] = 'failed'
        (dest / 'result.json').write_text(json.dumps(receipt, indent=2) + '\n')
        raise SystemExit(result.returncode)
receipt['status'] = 'pass'
receipt['commands'] = len(modules)
receipt['authored_graph_chart_sources'] = sum(e.get('authored_graph_chart_module', False) for e in entries)
receipt['authored_model_sources'] = sum(e['authored_model_module'] for e in entries)
receipt['live_sources_unchanged_after_replay'] = all(
    sha((project / e['path']).read_bytes()) == e['sha256'] for e in entries)
(dest / 'result.json').write_text(json.dumps(receipt, indent=2) + '\n')
if not receipt['live_sources_unchanged_after_replay']:
    raise SystemExit('Source bytes changed during replay; receipt is not a final source freeze.')
