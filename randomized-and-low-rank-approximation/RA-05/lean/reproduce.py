#!/usr/bin/env python3
"""Replay eleven RA-05 support exports locally; no Linux Comparator claim.

Requires the pinned Lean executable and already materialized pinned Lake
packages. Package sources are read-only. Fresh compiled objects are removed;
raw logs, source hashes, version and dependency checks go to --output.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--packages', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    project = Path(__file__).resolve().parent
    lean = args.lean.resolve()
    packages = args.packages.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    result = {'scope': 'Local source replay of eleven support theorems only',
              'whole_problem_verified': False, 'linux_isolation': False,
              'comparator_executed': False, 'raw_kernel_replay': False,
              'commands': [], 'pass': False}

    def dependencies() -> list:
        reports = []
        for package in manifest['packages']:
            path = packages / package['name']
            revision = subprocess.check_output(
                ['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
            status = subprocess.check_output(
                ['git', '-C', str(path), 'status', '--porcelain',
                 '--untracked-files=no'], text=True)
            reports.append({'name': package['name'], 'revision': revision,
                            'expected_revision': package['rev'],
                            'tracked_status': status})
            if revision != package['rev'] or status:
                raise RuntimeError('Pinned package revision/cleanliness mismatch: ' + str(path))
        return reports

    try:
        result['lean_version'] = subprocess.check_output([str(lean), '--version'], text=True)
        if 'version 4.33.1,' not in result['lean_version']:
            raise RuntimeError('Expected pinned Lean 4.33.1')
        result['lean_executable_sha256'] = sha(lean)
        result['dependencies_before'] = dependencies()
        lock = json.loads((project / 'PACKAGE_LOCK.json').read_text())
        for name, entry in lock['files'].items():
            if sha(project / name) != entry['sha256']:
                raise RuntimeError('Package source lock mismatch: ' + name)
        files = ['NLA/Statements/Infrastructure.lean', 'NLA/Statements/RA05.lean',
                 'NLA/Statements/RA06.lean', 'Reviewed/RA05.lean',
                 'NLA/Proofs/RA05/SupportMinimum.lean',
                 'NLA/Proofs/RA05/HyperplaneDefinitions.lean',
                 'NLA/Proofs/RA05/HyperplaneBridge.lean',
                 'Challenge.lean', 'Solution.lean', 'SupportAudit.lean', 'Identity.lean']
        with tempfile.TemporaryDirectory(prefix='nla-ra05-local-replay-') as temporary:
            env = os.environ.copy()
            env['LEAN_PATH'] = os.pathsep.join(
                [temporary] + [str(packages / p['name'] / '.lake/build/lib/lean')
                               for p in manifest['packages']] +
                [str(lean.parent.parent / 'lib/lean')])
            for name in files:
                source = project / name
                artifact = Path(temporary) / Path(name).with_suffix('.olean')
                artifact.parent.mkdir(parents=True, exist_ok=True)
                before = sha(source)
                command = [str(lean), '-R', str(project), '-o', str(artifact), str(source)]
                process = subprocess.run(command, env=env, cwd=project,
                                         capture_output=True, text=True, timeout=300)
                log = output / (name.replace('/', '-') + '.log')
                log.write_text(process.stdout + process.stderr)
                result['commands'].append({'source': name, 'source_sha256': before,
                                           'argv': command, 'exit_code': process.returncode,
                                           'log': log.name, 'log_sha256': sha(log)})
                print(name, process.returncode, flush=True)
                if process.returncode or sha(source) != before:
                    raise RuntimeError('Source compilation or immutability failed: ' + name)
        result['temporary_compiled_objects_removed'] = True
        result['dependencies_after'] = dependencies()
        result['pass'] = True
    except Exception as error:
        result['error'] = str(error)
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    return 0 if result['pass'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
